{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeSynonymInstances       #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Infer
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Damas-Milner type inference for ILC programs.
--
--------------------------------------------------------------------------------

module Language.ILC.Infer (
    inferExpr
  , inferTop
  ) where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Data.List (nub, partition)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Development.Placeholders
import Debug.Trace

import Language.ILC.Syntax
import Language.ILC.Type
import Language.ILC.TypeError

-- | Inference monad
type Infer a = (ReaderT
                  TypeEnv
                  (StateT
                  InferState
                  (Except
                    TypeError))
                  a)

-- | Inference state
newtype InferState = InferState { count :: Int }

-- | Initial inference state
initInfer :: InferState
initInfer = InferState { count = 0 }

data Constraint = TypeConstraint Type Type
                | ModeConstraint Mode Mode
                deriving (Eq, Show)

type Unifier = (Subst, [Constraint])

simplify :: [Constraint] -> [Constraint]
simplify cs = ts ++ ms'
  where
    (ts, ms) = partition (\case {TypeConstraint{} -> True ; _ -> False}) cs
    ms'      = simpfull ms
    
simpall :: [Constraint] -> Maybe [Constraint]
simpall ms = sequence $ map (\(ModeConstraint m1 m2) -> ModeConstraint <$> msimplify m1 <*> msimplify m2) ms

simpfull ms = if ms == ms' then ms else simpfull ms'
  where ms' = case simpall ms of
                Nothing -> error "mode error"
                Just x  -> x
      
-- | Constraint solver monad
type Solve a = ExceptT TypeError Identity a

newtype Subst = Subst (Map.Map TVar TM)
  deriving (Eq, Ord, Show, Monoid)

class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set.Set TVar

instance Substitutable Type where
  apply _ (TCon a) = TCon a
  apply (Subst s) t@(TVar a) = case Map.findWithDefault (T t) a s of
    T ty -> ty
    M _ -> t
  apply s (TArr t1 t2 m) = TArr (apply s t1) (apply s t2) (apply s m)
  apply s (TList t) = TList (apply s t)
  apply s (TProd ts) = TProd (apply s ts)
  apply s (TSet t) = TSet (apply s t)
  apply s (TRef t) = TRef (apply s t)
  apply s (TThunk t) = TThunk (apply s t)
  apply s (TRdChan t) = TRdChan (apply s t)
  apply s (TWrChan t) = TWrChan (apply s t)
  apply s TUsed = TUsed

  ftv (TVar a) = Set.singleton a
  ftv TCon{} = Set.empty
  ftv (TArr t1 t2 m) = ftv t1 `Set.union` ftv t2 `Set.union` ftv m
  ftv (TList t) = ftv t
  ftv (TProd ts) = ftv ts
  ftv (TSet t) = ftv t
  ftv (TRef t) = ftv t
  ftv (TThunk t) = ftv t
  ftv (TRdChan t) = ftv t
  ftv (TWrChan t) = ftv t
  ftv TUsed = Set.empty

instance Substitutable Mode where
  apply (Subst s) m@(MVar a) = case Map.findWithDefault (M m) a s of
    M mo -> mo
    T _  -> m
  apply (Subst s) m@(MVarVR a) = case Map.findWithDefault (M m) a s of
    M mo -> mo
    T _  -> m
  apply s (MSeq m1 m2) = MSeq (apply s m1) (apply s m2)
  apply _         m          = m

  ftv (MVar a) = Set.singleton a
  ftv (MVarVR a) = Set.singleton a
  ftv (MSeq m1 m2) = ftv m1 `Set.union` ftv m2
  ftv m        = Set.empty

instance Substitutable TM where
  apply s (T t) = T $ apply s t
  apply s (M m) = M $ apply s m

  ftv (T t) = ftv t
  ftv (M m) = ftv m

instance Substitutable (Scheme, Mode) where
  apply (Subst s) (Forall as t, m) = (Forall as $ apply s' t, m)
                          where s' = Subst $ foldr Map.delete s as
  ftv (Forall as t, _) = ftv t `Set.difference` Set.fromList as

instance Substitutable Constraint where
  apply s (TypeConstraint t1 t2) = TypeConstraint (apply s t1) (apply s t2)
  apply s (ModeConstraint m1 m2) = ModeConstraint (apply s m1) (apply s m2)
  
  ftv (TypeConstraint t1 t2) = ftv t1 `Set.union` ftv t2
  ftv (ModeConstraint t1 t2) = ftv t1 `Set.union` ftv t2

instance Substitutable a => Substitutable [a] where
  apply = fmap . apply

  ftv = foldr (Set.union . ftv) Set.empty

instance Substitutable TypeEnv where
  apply s (TypeEnv env) = TypeEnv $ Map.map (apply s) env
  ftv (TypeEnv env) = ftv $ Map.elems env

-- | Modes
parMode :: Mode -> Mode -> Infer Mode
parMode m1 m2 = case (m1, m2) of
  (W, V) -> return W
  (V, W) -> return W
  (W, R) -> return W
  (R, W) -> return W
  (R, R) -> return R
  (V, R) -> return R -- TODO: What mode compositions do we want?
  (R, V) -> return R
  (V, V) -> return V
  _      -> throwError $ ParFail m1 m2

seqMode :: Mode -> Mode -> Infer Mode
seqMode m1 m2 = case (m1, m2) of
  (V, m) -> return m
  (W, V) -> return W
  (R, _) -> return R
  (W, R) -> return W
  _      -> throwError $ SeqFail m1 m2

checkType :: Eq a => a -> a -> String -> Infer a
checkType ty1 ty2 msg = if ty1 == ty2 then return ty1
                        else throwError (TypeFail msg)

choiceMode :: Mode -> Mode -> Infer Mode
choiceMode m1 m2 = case (m1, m2) of
  (R, R) -> return R
  _        -> throwError $ ChoiceFail m1 m2

-------------------------------------------------------------------------------
-- Inference

-- | Run the inference monad
runInfer :: TypeEnv -> Infer (Type, [Constraint], Mode, TypeEnv) -> Either TypeError (Type, [Constraint], Mode, TypeEnv)
runInfer env m = runExcept $ evalStateT (runReaderT m env) initInfer

-- | Solve for toplevel type of an expression in a give environment
inferExpr :: TypeEnv -> Expr -> Either TypeError (Scheme, Mode)
inferExpr env ex = case runInfer env (infer ex) of
  Left err       -> Left err
  Right (ty, cs, m, _) -> case runSolve cs of
    Left err    -> Left err
    Right subst -> Right (closeOver $ apply subst ty, m)

-- | Return internal constraints used in solving for type of expression
constraintsExpr :: TypeEnv -> Expr -> Either TypeError ([Constraint], Subst, Type, Scheme)
constraintsExpr env ex = case runInfer env (infer ex) of
  Left       err -> Left err
  Right (ty, cs, _, _) -> case runSolve cs of
    Left err    -> Left err
    Right subst -> Right (cs, subst, ty, sc)
      where sc = closeOver $ apply subst ty

closeOver :: Type-> Scheme
closeOver = normalize . generalize emptyTyEnv

inEnv :: (Name, (Scheme, Mode)) -> Infer a -> Infer a
inEnv (x, sc) m = do
  let scope e = removeTyEnv e x `extendTyEnv` (x, sc)
  local scope m

lookupEnv :: Name -> Infer (Type, Mode)
lookupEnv x = do
  TypeEnv env <- ask
  case Map.lookup x env of
    Nothing -> throwError $ UnboundVariable x
    Just (tyA, m)  -> do ty <- instantiate tyA
                         return (ty, m)

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

{-fresh :: Infer Type
fresh = do
  s <- get
  put s{count = count s + 1}
  return $ TVar $ TV (letters !! count s)-}

fresh :: (String -> a) -> Infer a
fresh f = do
  s <- get
  put s{count = count s + 1}
  return $ f (letters !! count s)

instantiate :: Scheme -> Infer Type
instantiate (Forall as t) = do
  as' <- mapM (const (fresh (TVar . TV))) as
  let s = Subst $ Map.fromList $ zip as (map T as')
  return $ apply s t

generalize :: TypeEnv -> Type-> Scheme -- ^ T-Gen
generalize env t = Forall as t
  where as = Set.toList $ ftv t `Set.difference` ftv env

binops :: Binop -> Infer Type
binops Add = return $ TArr tyInt (TArr tyInt tyInt V) V
binops Sub = return $ TArr tyInt (TArr tyInt tyInt V) V
binops Mul = return $ TArr tyInt (TArr tyInt tyInt V) V
binops Div = return $ TArr tyInt (TArr tyInt tyInt V) V
binops Mod = return $ TArr tyInt (TArr tyInt tyInt V) V
binops And = return $ TArr tyBool (TArr tyBool tyBool V) V
binops Or  = return $ TArr tyBool (TArr tyBool tyBool V) V
binops Lt  = return $ TArr tyInt (TArr tyInt tyBool V) V
binops Gt  = return $ TArr tyInt (TArr tyInt tyBool V) V
binops Leq = return $ TArr tyInt (TArr tyInt tyBool V) V
binops Geq = return $ TArr tyInt (TArr tyInt tyBool V) V
binops Eql = eqbinop
binops Neq = eqbinop
binops _   = error "Infer.binops"

eqbinop :: Infer Type
eqbinop = do
  t1 <- fresh (TVar . TV)
  t2 <- fresh (TVar . TV)
  return $ TArr t1 (TArr t2 tyBool V) V

unops :: Unop -> Type
unops Not = TArr tyBool tyBool V

concatTCEs :: [(Type, [Constraint], [(Name, (Type, Mode))])]
           -> ([Type], [Constraint], [(Name, (Type, Mode))])
concatTCEs = foldr f ([], [], [])
  where
    f (t, c, e) (t', c', e') = (t : t', c ++ c', e ++ e')

concatTCs :: [(Type, [Constraint])] -> ([Type], [Constraint])
concatTCs = foldr f ([], [])
  where
    f (t, c) (t', c') = (t : t', c ++ c')

concatTCMs :: [(Type, [Constraint], Mode)] -> ([Type], [Constraint], [Mode])
concatTCMs = foldr f ([], [], [])
  where
    f (t, c, m) (t', c', m') = (t : t', c ++ c', m : m')

concatTCMEs :: [(Type, [Constraint], Mode, TypeEnv)] -> ([Type], [Constraint], [Mode], [TypeEnv])
concatTCMEs = foldr f ([], [], [], [])
  where
    f (t, c, m, e) (t', c', m', e') = (t : t', c ++ c', m : m', e : e')

inferPatList :: [Pattern]
             -> [Maybe Expr]
             -> Infer ([Type], [Constraint], [(Name, (Type, Mode))])
inferPatList pats exprs = do
  tces <- zipWithM inferPat pats exprs
  return $ concatTCEs tces

listConstraints :: [Type]
                -> [Constraint]
                -> Infer (Type, [Constraint])
listConstraints ts cs = do
  thd <- fresh (TVar . TV)
  return $ if null ts
           then (thd, cs)
           else (head ts, cs ++ map (TypeConstraint thd) ts)
        
inferPat :: Pattern
         -> Maybe Expr
         -> Infer (Type, [Constraint], [(Name, (Type, Mode))])
inferPat pat expr = case (pat, expr) of
  (PVar x, Just e) -> do
    tv <- fresh (TVar . TV)
    (te, ce, m, _) <- infer e
    let constraints = (TypeConstraint tv te) : ce
    return (tv, constraints, [(x, (tv, m))])
  (PVar x, Nothing) -> do
    tv <- fresh (TVar . TV)
    return (tv, [], [(x, (tv, V))])

  (PInt _, Just e) -> do
    (te, ce, _, _) <- infer e
    let constraints = (TypeConstraint te tyInt) : ce
    return (tyInt, constraints, [])
  (PInt _, Nothing) -> return (tyInt, [], [])

  (PBool _, Just e) -> do
    (te, ce, _, _) <- infer e
    let constraints = (TypeConstraint te tyBool) : ce
    return (tyBool, constraints, [])
  (PBool _, Nothing) -> return (tyBool, [], [])

  (PString _, Just e) -> do
    (te, ce, _, _) <- infer e
    let constraints = (TypeConstraint te tyString) : ce
    return (tyString, constraints, [])
  (PString _, Nothing) -> return (tyString, [], [])

  (PTag _, Just e) -> do
    (te, ce, _, _) <- infer e
    let constraints = (TypeConstraint te tyTag) : ce
    return (tyTag, constraints, [])

  (PTag _, Nothing) -> return (tyTag, [], [])

  (PTuple ps, Just (ETuple es)) -> do
    when (length ps /= length es) (error "fail") -- TODO: -- Custom error
    (tes, ces, _, _) <- infer $ ETuple es
    (ts, cs, env) <- inferPatList ps $ map Just es
    let constraints = TypeConstraint (TProd ts) tes : ces ++ cs
    return (TProd ts, constraints, env)
  (PTuple ps, Just e) -> do
    (ts, cs, env) <- inferPatList ps $ repeat Nothing
    (te, ce, _, _) <- infer e
    let constraints = TypeConstraint (TProd ts) te : cs ++ ce
    return (TProd ts, constraints, env)
  (PTuple ps, Nothing) -> do
    (ts, cs, env) <- inferPatList ps $ repeat Nothing
    return (TProd ts, cs, env)

  (PList ps, Just (EList es)) -> do
    when (length ps /= length es) (error "fail") -- TODO
    (tes, ces, _, _) <- infer $ EList es
    (ts, cs, env) <- inferPatList ps $ map Just es
    (thd, cs') <- listConstraints ts cs
    let constraints = TypeConstraint (TList thd) tes : ces ++ cs'
    return (TList thd, constraints, env)
  (PList ps, Just e) -> do
    (te, ce, _, _) <- infer e
    (ts, cs, env) <- inferPatList ps $ repeat Nothing
    (thd, cs') <- listConstraints ts cs
    let constraints = TypeConstraint (TList thd) te : ce ++ cs'
    return (TList thd, constraints, env)
  (PList ps, Nothing) -> do
    tces <- zipWithM inferPat ps $ repeat Nothing
    let (ts, cs, env) = concatTCEs tces
    (thd, cs') <- listConstraints ts cs
    return (TList thd, cs', env)

  (PSet ps, Just (ESett es)) -> do
    when (length ps /= length es) (error "fail") -- TODO
    (tes, ces, _, _) <- infer $ ESett es
    (ts, cs, env) <- inferPatList ps $ map Just es
    (thd, cs') <- listConstraints ts cs
    let constraints = TypeConstraint (TSet thd) tes : ces ++ cs'
    return (TSet thd, constraints, env)
  (PSet ps, Just e) -> do
    (te, ce, _, _) <- infer e
    (ts, cs, env) <- inferPatList ps $ repeat Nothing
    (thd, cs') <- listConstraints ts cs
    let constraints = TypeConstraint (TSet thd) te : ce ++ cs'
    return (TSet thd, constraints, env)
  (PSet ps, Nothing) -> do
    tces <- zipWithM inferPat ps $ repeat Nothing
    let (ts, cs, env) = concatTCEs tces
    (thd, cs') <- listConstraints ts cs
    return (TSet thd, cs', env)

  (PCons phd ptl, Just e@(EList (hd:tl))) -> do
    (te, ce, _, _) <- infer e
    (thd, chd, ehd) <- inferPat phd $ Just hd
    (ttl, ctl, etl) <- inferPat ptl $ Just $ EList tl
    let cs = ce ++ chd ++ ctl ++ [ TypeConstraint (TList thd) te
                                 , TypeConstraint te          ttl ]
        env = ehd ++ etl
    return (TList thd, cs, env)
  (PCons phd ptl, Just e) -> do
    (te, ce, _, _) <- infer e
    (thd, chd, ehd) <- inferPat phd Nothing
    (ttl, ctl, etl) <- inferPat ptl Nothing
    let cs = ce ++ chd ++ ctl ++ [ TypeConstraint (TList thd) te
                                 , TypeConstraint te ttl
                                 , TypeConstraint (TList thd) ttl ]
        env = ehd ++ etl
    return (TList thd, cs, env)
  (PCons phd ptl, Nothing) -> do
    (thd, chd, ehd) <- inferPat phd Nothing
    (ttl, ctl, etl) <- inferPat ptl Nothing
    let cs = TypeConstraint (TList thd) ttl : chd ++ ctl
        env = ehd ++ etl
    return (TList thd, cs, env)

  (PUnit, Just e) -> do
    (te, ce, _, _) <- infer e
    let constraints = TypeConstraint te tyUnit : ce
    return (tyUnit, constraints, [])
  (PUnit, Nothing) -> return (tyUnit, [], [])

  (PWildcard, Just _) -> do
    ty <- fresh (TVar . TV)
    return (ty, [], [])
  (PWildcard, Nothing) -> do
    ty <- fresh (TVar . TV)
    return (ty, [], [])

  (PCust x ps, Just (ECustom x' es)) -> do
    when (length ps /= length es) (error "fail1") -- TODO
    when (x /= x') (error "fail2") -- TODO
    (ts, cs, env) <- inferPatList ps $ map Just es
    return (tyMsg, cs, env)
  (PCust x ps, Just e) -> do
    (te, ce, _, _) <- infer e
    (ts, cs, env) <- inferPatList ps $ repeat Nothing
    let constraints = TypeConstraint tyMsg te : ce ++ cs
    return (tyMsg, constraints, env)
  (PCust x ps, Nothing) -> do
    tces <- zipWithM inferPat ps $ repeat Nothing
    let (ts, cs, env) = concatTCEs tces
    return (tyMsg, cs, env)

inferBranch :: Expr -> (Pattern, Expr, Expr) -> Infer (Type, [Constraint], Mode, TypeEnv)
inferBranch expr (pat, guard, branch) = do
  env <- ask
  (_, c1, binds) <- inferPat pat $ Just expr
  (_, _, _, _Γ2) <- infer expr
  case runSolve c1 of
    Left err -> throwError err
    Right sub -> do
      let sc t = generalize (apply sub env) (apply sub t)
      (t2, c2, m1, _Γ3) <- local (const _Γ2) (foldr (\(x, (t, m)) -> inEnv (x, (sc t, m)))
                        (local (apply sub) (infer guard))
                        binds)
      let moConstraints = ModeConstraint m1 V
      --unless (m1 == V) (throwError $ ModeFail "inferBranch")

      (t3, c3, m, _Γ4) <- local (const _Γ3) (foldr (\(x, (t, m)) -> inEnv (x, (sc t, m)))
                        (local (apply sub) (infer branch))
                        binds)
      let _Γ4' = foldl (\_Γ (x, _) -> removeTyEnv _Γ x) _Γ4 binds
          tyConstraints = TypeConstraint t2 tyBool :c1 ++ c2 ++ c3
          constraints = moConstraints : tyConstraints
      return (t3, constraints, m, _Γ4')

sameModes :: [Mode] -> String -> Either TypeError Mode
sameModes (m:ms) s = if (all ((==)m) ms) then Right m else Left $ ModeFail s

sameThings :: Eq a => [a] -> Either TypeError a
sameThings (m:ms) = if (all ((==)m) ms) then Right m else Left (TypeFail "Not same things.")

infer :: Expr -> Infer (Type, [Constraint], Mode, TypeEnv)
infer expr = case expr of
  EVar x -> do
    (tyA, m) <- lookupEnv x
    --unless (m == V) (throwError $ ModeFail "infer")
    _Γ1 <- ask
    _Γ2 <- case tyA of
          TRdChan _ -> return $ extendTyEnv _Γ1 (x, (closeOver TUsed, V))
          TUsed     -> do throwError LinearFail
          _         -> return _Γ1
    let constraints = [ModeConstraint m V]
    return (tyA, constraints, V, _Γ2)

  ELit (LInt _) -> do
    _Γ <- ask
    return (tyInt, [], V, _Γ)

  ELit (LBool _) -> do
    _Γ <- ask
    return (tyBool, [], V, _Γ)
    
  ELit (LString _) -> do
    _Γ <- ask
    return (tyString, [], V, _Γ)
    
  ELit (LTag _) -> do
    _Γ <- ask
    return (tyTag, [], V, _Γ)
  
  ELit LUnit -> do
    _Γ <- ask
    return (tyUnit, [], V, _Γ)
    
  ETuple es -> do
    _Γ1 <- ask
    -- TODO: Combine into one pass
    (_, _, _, _Γn) <- foldM (\(_, _, V, _Γ) e -> local (const _Γ) (infer e))
                      (tyUnit, [], V, _Γ1)
                      es
    tcmes <- mapM infer es
    let (tys, cs, ms, _) = concatTCMEs tcmes
    case sameModes (V:ms) "tuple" of
      Left err -> throwError err
      Right m -> do
        return (TProd tys, cs, m, _Γn)

  EList [] -> do
    _Γ <- ask
    tyV <- fresh (TVar . TV)
    return (TList tyV, [], V, _Γ)

  EList es -> do
    _Γ1 <- ask
    -- TODO: Combine into one pass
    (_, _, _, _Γn) <- foldM (\(_, _, V, _Γ) e -> local (const _Γ) (infer e))
                      (tyUnit, [], V, _Γ1)
                      es
    tcmes <- mapM infer es
    let tyFst = (\(x, _, _, _) -> x) $ head tcmes
        cs    = concatMap (\(_,x,_, _) -> x) tcmes
        cs'   = map (\(x, _, _, _) -> TypeConstraint tyFst x) tcmes
    return (TList tyFst, cs ++ cs', V, _Γ1)

  ESett [] -> do
    _Γ <- ask    
    tyV <- fresh (TVar . TV)
    return (TSet tyV, [], V, _Γ)
    
  ESett es -> do
    _Γ1 <- ask
    -- TODO: Combine into one pass
    (_, _, _, _Γn) <- foldM (\(_, _, V, _Γ) e -> local (const _Γ) (infer e))
                      (tyUnit, [], V, _Γ1)
                      es
    tcmes <- mapM infer es
    let tyFst = (\(x, _, _, _) -> x) $ head tcmes
        cs    = concatMap (\(_,x,_, _) -> x) tcmes
        cs'   = map (\(x, _, _, _) -> TypeConstraint tyFst x) tcmes
    return (TSet tyFst, cs ++ cs', V, _Γ1)

  EBin Cons e1 e2  -> do
   (tyA1, c1, m1, _Γ2) <- infer e1
   (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
   --unless (m1,m2) == (V,V)) (throwError $ ModeFail "cons")
   let tyConstraints = TypeConstraint (TList tyA1) tyA2 : c1 ++ c2
       moConstraints = [ModeConstraint m1 V, ModeConstraint m2 V]
       constraints = tyConstraints ++ moConstraints
   return (tyA2, constraints, V, _Γ3)

  EBin Concat e1 e2  -> do
   (tyA1, c1, m1, _Γ2) <- infer e1
   (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
   --unless ((m1,m2) == (V,V)) (throwError $ ModeFail "concat")
   let tyConstraints = TypeConstraint tyA1 tyA2 : c1 ++ c2
       moConstraints = [ModeConstraint m1 V, ModeConstraint m2 V]
       constraints = tyConstraints ++ moConstraints
   return (tyA1, constraints, V, _Γ3)

  EBin op e1 e2 -> do
    (tyA1, c1, m1, _Γ2) <- infer e1
    (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
    --unless ((m1,m2) == (V,V)) (throwError $ ModeFail "bin")
    tyV <- fresh (TVar . TV)
    let u1 = TArr tyA1 (TArr tyA2 tyV V) V
    u2 <- binops op
    let tyConstraints = c1 ++ c2 ++ [ TypeConstraint u1 u2
                                  , TypeConstraint tyA1 tyA2]
        moConstraints = [ModeConstraint m1 V, ModeConstraint m2 V]
        constraints = tyConstraints ++ moConstraints
    return (tyV, constraints, V, _Γ3)

  EUn op e -> do
    (tyA, c, m, _Γ2) <- infer e
    --unless (m == V) (throwError $ ModeFail "un")
    tyV <- fresh (TVar . TV)
    let u1 = TArr tyA tyV V
        u2 = unops op
        tyConstraints = TypeConstraint u1 u2 : c
        moConstraints = [ModeConstraint m V]
        constraints = tyConstraints ++ moConstraints
    return (tyV, constraints, V, _Γ2)

  EIf e1 e2 e3 -> do
    (tyA1, c1, m1, _Γ2) <- infer e1
    (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
    (tyA3, c3, m2', _Γ3') <- local (const _Γ2) (infer e3)
    --unless (m1 == V) (throwError $ ModeFail "if")
    -- TODO: Mode constraints
    _ <- checkType _Γ3 _Γ3' "Branches have different outgoing typing contexts."
    _ <- checkType m2  m2'  "Branches have different modes."
    when (m2 /= m2') (error "modes")
    --m3 <- seqMode m1 m2
    m3 <- fresh (MVar . TV)
    let tyConstraints = c1 ++ c2 ++ c3 ++ [ TypeConstraint tyA1 tyBool
                                        , TypeConstraint tyA2 tyA3 ]
        moConstraints = [ModeConstraint m1 V, ModeConstraint (MSeq m1 m2) m3]
        constraints = tyConstraints ++ moConstraints
    return (tyA2, constraints, m3, _Γ3)

  ELet p e1 e2 -> do
    env <- ask
    (_, c1, binds) <- inferPat p $ Just e1
    (_, _, m1, _Γ2) <- infer e1
    case runSolve c1 of
      Left err -> throwError err
      Right sub -> do
        let sc t = generalize (apply sub env) (apply sub t)
        (tyB, c2, m2, _Γ3) <- local (const _Γ2) (foldr (\(x, (t, m)) -> inEnv (x, (sc t, m)))
                              (local (apply sub) (infer e2))
                              binds)
        --m3 <-  seqMode m1 m2
        m3 <- fresh (MVar . TV)
        let tyConstraints = c1 ++ c2
            moConstraints = [ModeConstraint (MSeq m1 m2) m3]
            constraints = tyConstraints ++ moConstraints
        return (tyB, constraints, m3, _Γ3)

  EMatch e bs -> do
    tcmes <- mapM (inferBranch e) bs
    let (ts, cs, ms, _Γs) = concatTCMEs tcmes
        ty       = head ts
        cs'      = map (\(t1,t2) -> TypeConstraint t1 t2) $ zip (tail ts) (repeat ty)
    -- TODO: Clean up
    let envs = map (\case {TypeEnv binds -> Map.filter (\x -> fst x == (Forall
    [] TUsed)) binds}) _Γs
    _ <- case sameThings envs  of
             Left err -> throwError err
             Right _Γ  -> return _Γ
    case sameModes ms "match" of
      Left err -> throwError err
      Right m -> do
        return (ty, cs ++ cs', m, head _Γs)

  ELam (PVar x) e -> do
    tyV <- fresh (TVar . TV)
    (tyA, c, m, _Γ2) <- inEnv (x, (Forall [] tyV, V)) (infer e)
    return (TArr tyV tyA m, c, V, _Γ2)

  ELam PUnit e -> do
    (tyA, c, m, _Γ2) <- infer e
    return (TArr tyUnit tyA m, c, V, _Γ2)

  ELam PWildcard e -> do
    tyV <- fresh (TVar . TV)
    (tyA, c, m, _Γ2) <- infer e
    return (TArr tyV tyA m , c, V, _Γ2)

  ELam _ _ -> error "Infer.infer: ELam"

  EFix e -> do
    (tyA2A, c, m, _Γ2) <- infer e
    --unless (m == V) (throwError $ ModeFail "fix")
    tyV <- fresh (TVar . TV)
    mV <- fresh (MVar . TV)
    let tyConstraints = TypeConstraint tyA2A (TArr tyV tyV mV) : c
        moConstraints  = [ModeConstraint m V]
        constraints = tyConstraints ++ moConstraints
    return (tyV, constraints, V, _Γ2)

  EApp e1 e2 -> do
    (tyA, c1, m1, _Γ2) <- infer e2
    (tyA2B, c2, m2, _Γ3) <- local (const _Γ2) (infer e1)
    --unless ((m1,m2) == (V,V)) (throwError $ ModeFail "app")
    tyV <- fresh (TVar . TV)
    mV <- fresh (MVar . TV)
    let tyConstraints = TypeConstraint tyA2B (TArr tyA tyV mV) : c1 ++ c2
        moConstraints = [ModeConstraint  m1 V, ModeConstraint m2 V]
        constraints = tyConstraints ++ moConstraints
    return (tyV, constraints, mV, _Γ3)

  ERd e -> do
    (tyA, c, m, _Γ2) <- infer e
    --unless (m == V) (throwError $ ModeFail "rd")
    tyV <- fresh (TVar . TV)
    let tyConstraints = TypeConstraint tyA (TRdChan tyV) : c
        moConstraints = [ModeConstraint m V]
        constraints = tyConstraints ++ moConstraints
    return (TProd [tyV, TRdChan tyV], constraints, R, _Γ2)

  EWr e1 e2 -> do
    (tyA1, c1, m1, _Γ2) <- infer e1
    (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
    unless ((m1,m2) == (V,V)) (throwError $ ModeFail "wr")
    let constraints = TypeConstraint tyA2 (TWrChan tyA1) : c1 ++ c2
    return (tyUnit, constraints, W, _Γ3)

  ENu (rdc, wrc) e -> do
    tyV <- fresh (TVar . TV)
    let newChans = [ (rdc, (Forall [] $ TRdChan tyV, V))
                   , (wrc, (Forall [] $ TWrChan tyV, V))]
    (tyA, c, m, _Γ2) <- foldr inEnv (infer e) newChans
    return (tyA, c , m, _Γ2)

  EFork e1 e2 -> do
    (_, c1, m1, _Γ2) <- infer e1
    (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
    --m3 <- parMode m1 m2
    m3 <- fresh (MVar . TV)
    let tyConstraints = c1 ++ c2
        moConstraints = [ModeConstraint (MPar m1 m2) m3]
        constraints = tyConstraints ++ moConstraints
    return (tyA2, constraints, m3, _Γ2)

  EChoice e1 e2 -> do
    (tyA1, c1, m1, _Γ2) <- infer e1
    (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
    --m <- choiceMode m1 m2
    let tyConstraints = TypeConstraint tyA1 tyA2 : c1 ++ c2
        moConstraints = [ModeConstraint m1 R, ModeConstraint m2 R]
        constraints = tyConstraints ++ moConstraints
    return (tyA1, constraints, R, _Γ3)

  ESeq e1 e2 -> do
    (_, c1, m1, _Γ2) <- infer e1
    (t2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
    --m3 <- seqMode m1 m2
    m3 <- fresh (MVar . TV)
    let tyConstraints = c1 ++ c2
        moConstraints = [ModeConstraint (MSeq m1 m2) m3]
        constraints = tyConstraints ++ moConstraints
    return (t2, constraints, m3, _Γ3)

  ERef e -> do
    (tyA, c, m, _Γ2) <- infer e
    --unless (m == V) (throwError $ ModeFail "ref")
    tyV <- fresh (TVar . TV)
    let tyConstraints = TypeConstraint tyV (TRef tyA) : c
        moConstraints = [ModeConstraint m V]
        constraints = tyConstraints ++ moConstraints
    return (tyV, constraints, V, _Γ2)

  EGet e -> do
    (tyA, c, m, _Γ2) <- infer e
    --unless (m == V) (throwError $ ModeFail "get")
    tyV <- fresh (TVar . TV)
    let tyConstraints = TypeConstraint (TRef tyV) tyA : c
        moConstraints = [ModeConstraint m V]
        constraints = tyConstraints ++ moConstraints
    return (tyV, constraints, V, _Γ2)

  ESet x e -> do -- TODO: Change to ESet e1 e2
    (tyA1, mx) <- lookupEnv x
    (tyA2, c, m, _Γ2) <- infer e
    --unless (m == V) (throwError $ ModeFail "set")
    let tyConstraints = TypeConstraint tyA1 (TRef tyA2) : c
        moConstraints = [ModeConstraint m V]
        constraints = tyConstraints ++ moConstraints
    return (tyUnit, constraints, V, _Γ2)

  EThunk e -> do  -- TODO
    (tyA, c, m, _Γ2) <- infer e
    --unless (m == V) (throwError $ ModeFail "thunk")
    tyV <- fresh (TVar . TV)
    let tyConstraints = TypeConstraint tyV (TThunk tyA) : c
        moConstraints = [ModeConstraint m V]
        constraints = tyConstraints ++ moConstraints
    return (tyV, constraints, V, _Γ2)

  EForce e -> do  -- TODO
    (tyA, c, m, _Γ2) <- infer e
    --unless (m == V) (throwError $ ModeFail "force")
    tyV <- fresh (TVar . TV)
    let tyConstraints = TypeConstraint (TThunk tyV) tyA : c
        moConstraints = [ModeConstraint m V]
        constraints = tyConstraints ++ moConstraints
    return (tyV, constraints, m, _Γ2)

  EPrint e -> do
    (_, c, m, _Γ2) <- infer e
    --unless (m == V) (throwError $ ModeFail "print")
    return (tyUnit, ModeConstraint m V : c, V, _Γ2)

  EError e  -> do
    tyV <- fresh (TVar . TV)
    (tyA, c, m, _Γ2) <- infer e
    --unless (m == V) (throwError $ ModeFail "error")
    let tyConstraints = TypeConstraint tyA tyString : c
        moConstraints = [ModeConstraint m V]
        constraints = tyConstraints ++ moConstraints
    return (tyV, constraints, V, _Γ2)

  ECustom x es -> do
    _Γ <- ask
    return (tyMsg, [], V, _Γ)

inferTop :: TypeEnv -> [(Name, Expr)] -> Either TypeError TypeEnv
inferTop env [] = Right env
inferTop env ((name, ex):xs) = case inferExpr env ex of
  Left err -> Left err
  Right (ty, m) -> inferTop (extendTyEnv env (name, (ty, m))) xs

normalize :: Scheme -> Scheme
normalize (Forall _ body) = Forall (map snd ord) (normtype body)
  where
    ord = zip (nub $ fv body) (map TV letters)

    fv (TVar a) = [a]
    fv (TArr a b m) = fv a ++ fv b ++ fvm m
    fv (TCon _) = []
    fv (TList a) = fv a
    fv (TProd as) = concatMap fv as
    fv (TSet a) = fv a
    fv (TRef a) = fv a
    fv (TThunk a) = fv a
    fv (TRdChan a) = fv a
    fv (TWrChan a) = fv a
    fv TUsed = []

    fvm (MVar a) = [a]
    fvm (MSeq m1 m2) = fvm m1 ++ fvm m2
    fvm m        = []
    
    normtype (TVar a)   =
        case Prelude.lookup a ord of
            Just x -> TVar x
            Nothing -> error "type variable not in signature"
    normtype (TCon a)   = TCon a
    -- TODO: normalize modes
    normtype (TArr a b m) = TArr (normtype a) (normtype b) (normmode m)
    normtype (TList a)   = TList (normtype a)
    normtype (TProd as)   = TProd (map normtype as)
    normtype (TSet a)   = TSet (normtype a)
    normtype (TRef a)   = TRef (normtype a)
    normtype (TThunk a)   = TThunk (normtype a)
    normtype (TRdChan a)   = TRdChan (normtype a)
    normtype (TWrChan a)   = TWrChan (normtype a)
    normtype TUsed   = TUsed

    normmode (MVar a) =
        case Prelude.lookup a ord of
            Just x -> MVar x
            Nothing -> error "mode variable not in signature"
    normmode (MSeq m1 m2) = MSeq (normmode m1) (normmode m2)
    normmode m        = m
    
-------------------------------------------------------------------------------
-- Constraint Solver
-------------------------------------------------------------------------------

emptySubst :: Subst
emptySubst = mempty

compose :: Subst -> Subst -> Subst
(Subst s1) `compose` (Subst s2) = Subst $ Map.map (apply (Subst s1)) s2 `Map.union` s1

runSolve :: [Constraint] -> Either TypeError Subst
runSolve cs = runIdentity $ runExceptT $ solver st
  where st = (emptySubst, simplify cs)

unifyMany :: [TM] -> [TM] -> Solve Subst
unifyMany [] []  = return emptySubst
unifyMany (t1 : ts1) (t2 : ts2) =
  do su1 <- unifies t1 t2
     su2 <- unifyMany (apply su1 ts1) (apply su1 ts2)
     return (su2 `compose` su1)
unifyMany t1 t2 = throwError $ UnificationMismatch t1 t2

unifies :: TM -> TM -> Solve Subst
unifies t1 t2 | t1 == t2 = return emptySubst
unifies (T (TVar v)) (T t) = v `bind` (T t)
unifies (T t) (T (TVar v)) = v `bind` (T t)
unifies (T (TArr t1 t2 m1)) (T (TArr t3 t4 m2)) = unifyMany [T t1, T t2, M m1] [T t3, T t4, M m2]
unifies (T (TList t1)) (T (TList t2)) = unifies (T t1) (T t2)
unifies (T (TProd ts1)) (T (TProd ts2)) = unifyMany (map T ts1) (map T ts2)
unifies (T (TSet t1)) (T (TSet t2)) = unifies (T t1) (T t2)
unifies (T (TRef t1)) (T (TRef t2)) = unifies (T t1) (T t2)
unifies (T (TThunk t1)) (T (TThunk t2)) = unifies (T t1) (T t2)
unifies (T (TRdChan t1)) (T (TRdChan t2)) = unifies (T t1) (T t2)
unifies (T (TWrChan t1)) (T (TWrChan t2)) = unifies (T t1) (T t2)

unifies (M (MVar v)) (M t) = v `bind` (M t)
unifies (M t) (M (MVar v)) = v `bind` (M t)
unifies (M (MVarVR v)) (M t) = v `bind` (M t)
unifies (M t) (M (MVarVR v)) = v `bind` (M t)
unifies (M (MSeq m1 m2)) (M (MSeq m3 m4)) = unifyMany [M m1, M m2] [M m3, M m4]
unifies (M (MPar m1 m2)) (M (MPar m3 m4)) = unifyMany [M m1, M m2] [M m3, M m4]
unifies t1 t2 = throwError $ UnificationFail t1 t2

solver :: Unifier -> Solve Subst
solver (su, cs) =
  case cs of
    [] -> return $ su
    (TypeConstraint t1 t2 : cs') -> do
      su1 <- unifies (T t1) (T t2)
      solver (su1 `compose` su, apply su1 cs')
    (ModeConstraint m1 m2 : cs') -> do
      su1 <- unifies (M m1) (M m2)
      solver (su1 `compose` su, apply su1 cs')
         
bind :: TVar -> TM -> Solve Subst
bind a (T t) | t == TVar a     = return emptySubst
             | occursCheck a t = throwError $ InfiniteType a t
             | otherwise       = return (Subst $ Map.singleton a (T t))
bind a (M t) | t == MVar a     = return emptySubst
             | t == MVarVR a   = return emptySubst
             | otherwise       = return (Subst $ Map.singleton a (M t))

occursCheck :: Substitutable a => TVar -> a -> Bool
occursCheck a t = a `Set.member` ftv t
