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
import Data.List (nub)
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

type Constraint = (Type, Type)

type Unifier = (Subst, [Constraint])

-- | Constraint solver monad
type Solve a = ExceptT TypeError Identity a

newtype Subst = Subst (Map.Map TVar Type)
  deriving (Eq, Ord, Show, Monoid)

class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set.Set TVar

instance Substitutable Type where
  apply _ (TCon a) = TCon a
  apply (Subst s) t@(TVar a) = Map.findWithDefault t a s
  apply s (TArr t1 t2 m) = TArr (apply s t1) (apply s t2) m
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
  ftv (TArr t1 t2 _) = ftv t1 `Set.union` ftv t2
  ftv (TList t) = ftv t
  ftv (TProd ts) = ftv ts
  ftv (TSet t) = ftv t
  ftv (TRef t) = ftv t
  ftv (TThunk t) = ftv t
  ftv (TRdChan t) = ftv t
  ftv (TWrChan t) = ftv t
  ftv TUsed = Set.empty

instance Substitutable (Scheme, Mode) where
  apply (Subst s) (Forall as t, m) = (Forall as $ apply s' t, m)
                          where s' = Subst $ foldr Map.delete s as
  ftv (Forall as t, _) = ftv t `Set.difference` Set.fromList as

instance Substitutable Constraint where
  apply s (t1, t2) = (apply s t1, apply s t2)
  ftv (t1, t2) = ftv t1 `Set.union` ftv t2

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
  let s = Subst $ Map.fromList $ zip as as'
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
           else (head ts, cs ++ map (thd,) ts)
        
inferPat :: Pattern
         -> Maybe Expr
         -> Infer (Type, [Constraint], [(Name, (Type, Mode))])
inferPat pat expr = case (pat, expr) of
  (PVar x, Just e) -> do
    tv <- fresh (TVar . TV)
    (te, ce, m, _) <- infer e
    return (tv, (tv, te) : ce, [(x, (tv, m))])
  (PVar x, Nothing) -> do
    tv <- fresh (TVar . TV)
    return (tv, [], [(x, (tv, V))])

  (PInt _, Just e) -> do
    (te, ce, _, _) <- infer e
    return (tyInt, (te, tyInt) : ce, [])
  (PInt _, Nothing) -> return (tyInt, [], [])

  (PBool _, Just e) -> do
    (te, ce, _, _) <- infer e
    return (tyBool, (te, tyBool) : ce, [])
  (PBool _, Nothing) -> return (tyBool, [], [])

  (PString _, Just e) -> do
    (te, ce, _, _) <- infer e
    return (tyString, (te, tyString) : ce, [])
  (PString _, Nothing) -> return (tyString, [], [])

  (PTag _, Just e) -> do
    (te, ce, _, _) <- infer e
    return (tyTag, (te, tyTag) : ce, [])
  (PTag _, Nothing) -> return (tyTag, [], [])

  (PTuple ps, Just (ETuple es)) -> do
    when (length ps /= length es) (error "fail") -- TODO: -- Custom error
    (tes, ces, _, _) <- infer $ ETuple es
    (ts, cs, env) <- inferPatList ps $ map Just es
    return (TProd ts, ces ++ cs ++ [(TProd ts, tes)], env)
  (PTuple ps, Just e) -> do
    (ts, cs, env) <- inferPatList ps $ repeat Nothing
    (te, ce, _, _) <- infer e
    return (TProd ts, cs ++ ce ++ [(TProd ts, te)], env)
  (PTuple ps, Nothing) -> do
    (ts, cs, env) <- inferPatList ps $ repeat Nothing
    return (TProd ts, cs, env)

  (PList ps, Just (EList es)) -> do
    when (length ps /= length es) (error "fail") -- TODO
    (tes, ces, _, _) <- infer $ EList es
    (ts, cs, env) <- inferPatList ps $ map Just es
    (thd, cs') <- listConstraints ts cs
    return (TList thd, ces ++ cs' ++ [(TList thd, tes)], env)
  (PList ps, Just e) -> do
    (te, ce, _, _) <- infer e
    (ts, cs, env) <- inferPatList ps $ repeat Nothing
    (thd, cs') <- listConstraints ts cs
    return (TList thd, ce ++ cs' ++ [(TList thd, te)], env)
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
    return (TSet thd, ces ++ cs' ++ [(TSet thd, tes)], env)
  (PSet ps, Just e) -> do
    (te, ce, _, _) <- infer e
    (ts, cs, env) <- inferPatList ps $ repeat Nothing
    (thd, cs') <- listConstraints ts cs
    return (TSet thd, ce ++ cs' ++ [(TSet thd, te)], env)
  (PSet ps, Nothing) -> do
    tces <- zipWithM inferPat ps $ repeat Nothing
    let (ts, cs, env) = concatTCEs tces
    (thd, cs') <- listConstraints ts cs
    return (TSet thd, cs', env)

  (PCons phd ptl, Just e@(EList (hd:tl))) -> do
    (te, ce, _, _) <- infer e
    (thd, chd, ehd) <- inferPat phd $ Just hd
    (ttl, ctl, etl) <- inferPat ptl $ Just $ EList tl
    let cs = ce ++ chd ++ ctl ++ [(te, TList thd), (te, ttl)]
        env = ehd ++ etl
    return (TList thd, cs, env)
  (PCons phd ptl, Just e) -> do
    (te, ce, _, _) <- infer e
    (thd, chd, ehd) <- inferPat phd Nothing
    (ttl, ctl, etl) <- inferPat ptl Nothing
    let cs = ce ++ chd ++ ctl ++ [ (te, TList thd)
                                 , (te, ttl)
                                 , (TList thd, ttl) ]
        env = ehd ++ etl
    return (TList thd, cs, env)
  (PCons phd ptl, Nothing) -> do
    (thd, chd, ehd) <- inferPat phd Nothing
    (ttl, ctl, etl) <- inferPat ptl Nothing
    let cs = chd ++ ctl ++ [(TList thd, ttl)]
        env = ehd ++ etl
    return (TList thd, cs, env)

  (PUnit, Just e) -> do
    (te, ce, _, _) <- infer e
    return (tyUnit, ce ++ [(te, tyUnit)], [])
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
    return (tyMsg, ce ++ cs ++ [(tyMsg, te)], env)
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
      unless (m1 == V) (throwError $ ModeFail "inferBranch")

      (t3, c3, m, _Γ4) <- local (const _Γ3) (foldr (\(x, (t, m)) -> inEnv (x, (sc t, m)))
                        (local (apply sub) (infer branch))
                        binds)
      let _Γ4' = foldl (\_Γ (x, _) -> removeTyEnv _Γ x) _Γ4 binds
      return (t3, c1 ++ c2 ++ c3 ++ [(t2, tyBool)], m, _Γ4')

sameModes :: [Mode] -> String -> Either TypeError Mode
sameModes (m:ms) s = if (all ((==)m) ms) then Right m else Left $ ModeFail s

sameThings :: Eq a => [a] -> Either TypeError a
sameThings (m:ms) = if (all ((==)m) ms) then Right m else Left (TypeFail "Not same things.")

infer :: Expr -> Infer (Type, [Constraint], Mode, TypeEnv)
infer expr = case expr of
  EVar x -> do
    (tyA, m) <- lookupEnv x
    unless (m == V) (throwError $ ModeFail "infer")
    _Γ1 <- ask
    _Γ2 <- case tyA of
          TRdChan _ -> return $ extendTyEnv _Γ1 (x, (closeOver TUsed, V))
          TUsed     -> do throwError LinearFail
          _         -> return _Γ1
    return (tyA, [], V, _Γ2)

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
        cs'   = map (\(x, _, _, _) -> (tyFst, x)) tcmes
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
        cs'   = map (\(x, _, _, _) -> (tyFst, x)) tcmes
    return (TSet tyFst, cs ++ cs', V, _Γ1)

  EBin Cons e1 e2  -> do
   (tyA1, c1, m1, _Γ2) <- infer e1
   (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
   unless ((m1,m2) == (V,V)) (throwError $ ModeFail "cons")
   return (tyA2, c1 ++ c2 ++ [(TList tyA1, tyA2)], V, _Γ3)

  EBin Concat e1 e2  -> do
   (tyA1, c1, m1, _Γ2) <- infer e1
   (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
   unless ((m1,m2) == (V,V)) (throwError $ ModeFail "concat")
   return (tyA1, c1 ++ c2 ++ [(tyA1, tyA2)], V, _Γ3)

  EBin op e1 e2 -> do
    (tyA1, c1, m1, _Γ2) <- infer e1
    (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
    unless ((m1,m2) == (V,V)) (throwError $ ModeFail "bin")
    tyV <- fresh (TVar . TV)
    let u1 = TArr tyA1 (TArr tyA2 tyV V) V
    u2 <- binops op
    return (tyV, c1 ++ c2 ++ [(u1, u2), (tyA1, tyA2)], V, _Γ3)

  EUn op e -> do
    (tyA, c, m, _Γ2) <- infer e
    unless (m == V) (throwError $ ModeFail "un")
    tyV <- fresh (TVar . TV)
    let u1 = TArr tyA tyV V
        u2 = unops op
    return (tyV, c ++ [(u1, u2)], V, _Γ2)

  EIf e1 e2 e3 -> do
    (tyA1, c1, m1, _Γ2) <- infer e1
    (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
    (tyA3, c3, m2', _Γ3') <- local (const _Γ2) (infer e3)
    unless (m1 == V) (throwError $ ModeFail "if")
    _ <- checkType _Γ3 _Γ3' "Branches have different outgoing typing contexts."
    _ <- checkType m2  m2'  "Branches have different modes."
    when (m2 /= m2') (error "modes")
    m3 <- seqMode m1 m2
    return (tyA2, c1 ++ c2 ++ c3 ++ [(tyA1, tyBool), (tyA2, tyA3)], m3, _Γ3)

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
        m3 <-  seqMode m1 m2
        return (tyB, c1 ++ c2, m3, _Γ3)

  EMatch e bs -> do
    tcmes <- mapM (inferBranch e) bs
    let (ts, cs, ms, _Γs) = concatTCMEs tcmes
        ty       = head ts
        cs'      = zip (tail ts) (repeat ty)
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
    return (TArr tyV tyA m , c, V, _Γ2)

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
    unless (m == V) (throwError $ ModeFail "fix")
    tyV <- fresh (TVar . TV)
    mV <- fresh MVar
    return (tyV, c ++ [(tyA2A, TArr tyV tyV mV)], mV, _Γ2)

  EApp e1 e2 -> do
    (tyA, c1, m1, _Γ2) <- infer e2
    (tyA2B, c2, m2, _Γ3) <- local (const _Γ2) (infer e1)
    unless ((m1,m2) == (V,V)) (throwError $ ModeFail "app")
    tyV <- fresh (TVar . TV)
    mV <- fresh MVar
    return (tyV, c1 ++ c2 ++ [(tyA2B, TArr tyA tyV mV)], mV, _Γ3)

  ERd e -> do
    (tyA, c, m, _Γ2) <- infer e
    unless (m == V) (throwError $ ModeFail "rd")
    tyV <- fresh (TVar . TV)
    return (TProd [tyV, TRdChan tyV], c ++ [(tyA, TRdChan tyV)], R, _Γ2)

  EWr e1 e2 -> do
    (tyA1, c1, m1, _Γ2) <- infer e1
    (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
    unless ((m1,m2) == (V,V)) (throwError $ ModeFail "wr")
    return (tyUnit, c1 ++ c2 ++ [(tyA2, TWrChan tyA1)], W, _Γ3)

  ENu (rdc, wrc) e -> do
    tyV <- fresh (TVar . TV)
    let newChans = [ (rdc, (Forall [] $ TRdChan tyV, V))
                   , (wrc, (Forall [] $ TWrChan tyV, V))]
    (tyA, c, m, _Γ2) <- foldr inEnv (infer e) newChans
    return (tyA, c , m, _Γ2)

  EFork e1 e2 -> do
    (_, c1, m1, _Γ2) <- infer e1
    (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
    m3 <- parMode m1 m2
    return (tyA2, c1 ++ c2, m3, _Γ2)

  EChoice e1 e2 -> do
    (tyA1, c1, m1, _Γ2) <- infer e1
    (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
    m <- choiceMode m1 m2
    return (tyA1, c1 ++ c2 ++ [(tyA1, tyA2)], m, _Γ3)

  ESeq e1 e2 -> do
    (_, c1, m1, _Γ2) <- infer e1
    (t2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
    m3 <- seqMode m1 m2
    return (t2, c1 ++ c2, m3, _Γ3)

  ERef e -> do
    (tyA, c, m, _Γ2) <- infer e
    unless (m == V) (throwError $ ModeFail "ref")
    tyV <- fresh (TVar . TV)
    return (tyV, c ++ [(tyV, TRef tyA)], V, _Γ2)

  EGet e -> do
    (tyA, c, m, _Γ2) <- infer e
    unless (m == V) (throwError $ ModeFail "get")
    tyV <- fresh (TVar . TV)
    return (tyV, c ++ [(TRef tyV, tyA)], V, _Γ2)

  ESet x e -> do -- TODO: Change to ESet e1 e2
    (tyA1, mx) <- lookupEnv x
    (tyA2, c, m, _Γ2) <- infer e
    unless (m == V) (throwError $ ModeFail "set")
    return (tyUnit, c ++ [(tyA1, TRef tyA2)], V, _Γ2)

  EThunk e -> do  -- TODO
    (tyA, c, m, _Γ2) <- infer e
    unless (m == V) (throwError $ ModeFail "thunk")
    tyV <- fresh (TVar . TV)
    return (tyV, c ++ [(tyV, TThunk tyA)], V, _Γ2)

  EForce e -> do  -- TODO
    (tyA, c, m, _Γ2) <- infer e
    unless (m == V) (throwError $ ModeFail "force")
    tyV <- fresh (TVar . TV)
    return (tyV, c ++ [(TThunk tyV, tyA)], m, _Γ2)

  EPrint e -> do
    (_, c, m, _Γ2) <- infer e
    unless (m == V) (throwError $ ModeFail "print")
    return (tyUnit, c, V, _Γ2)

  EError e  -> do
    tyV <- fresh (TVar . TV)
    (tyA, c, m, _Γ2) <- infer e
    unless (m == V) (throwError $ ModeFail "error")
    return (tyV, c ++ [(tyA, tyString)], V, _Γ2)

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
    fv (TArr a b _) = fv a ++ fv b
    fv (TCon _) = []
    fv (TList a) = fv a
    fv (TProd as) = concatMap fv as
    fv (TSet a) = fv a
    fv (TRef a) = fv a
    fv (TThunk a) = fv a
    fv (TRdChan a) = fv a
    fv (TWrChan a) = fv a
    fv TUsed = []
    
    normtype (TVar a)   =
        case Prelude.lookup a ord of
            Just x -> TVar x
            Nothing -> error "type variable not in signature"
    normtype (TCon a)   = TCon a
    -- TODO: normalize modes
    normtype (TArr a b m) = TArr (normtype a) (normtype b) m
    normtype (TList a)   = TList (normtype a)
    normtype (TProd as)   = TProd (map normtype as)
    normtype (TSet a)   = TSet (normtype a)
    normtype (TRef a)   = TRef (normtype a)
    normtype (TThunk a)   = TThunk (normtype a)
    normtype (TRdChan a)   = TRdChan (normtype a)
    normtype (TWrChan a)   = TWrChan (normtype a)
    normtype TUsed   = TUsed
    
-------------------------------------------------------------------------------
-- Constraint Solver
-------------------------------------------------------------------------------

emptySubst :: Subst
emptySubst = mempty

compose :: Subst -> Subst -> Subst
(Subst s1) `compose` (Subst s2) = Subst $ Map.map (apply (Subst s1)) s2 `Map.union` s1

runSolve :: [Constraint] -> Either TypeError Subst
runSolve cs = runIdentity $ runExceptT $ solver st
  where st = (emptySubst, cs)

unifyMany :: [Type] -> [Type] -> Solve Subst
unifyMany [] []  = return emptySubst
unifyMany (t1 : ts1) (t2 : ts2) =
  do su1 <- unifies t1 t2
     su2 <- unifyMany (apply su1 ts1) (apply su1 ts2)
     return (su2 `compose` su1)
unifyMany t1 t2 = throwError $ UnificationMismatch t1 t2

unifies :: Type-> Type-> Solve Subst
unifies t1 t2 | t1 == t2 = return emptySubst
unifies (TVar v) t = v `bind` t
unifies t (TVar v) = v `bind` t
-- TODO: m1 == m2?
unifies (TArr t1 t2 m1) (TArr t3 t4 m2) = unifyMany [t1, t2] [t3, t4]
unifies (TList t1) (TList t2) = unifies t1 t2
unifies (TProd ts1) (TProd ts2) = unifyMany ts1 ts2
unifies (TSet t1) (TSet t2) = unifies t1 t2
unifies (TRef t1) (TRef t2) = unifies t1 t2
unifies (TThunk t1) (TThunk t2) = unifies t1 t2
unifies (TRdChan t1) (TRdChan t2) = unifies t1 t2
unifies (TWrChan t1) (TWrChan t2) = unifies t1 t2
unifies t1 t2 = throwError $ UnificationFail t1 t2

solver :: Unifier -> Solve Subst
solver (su, cs) =
  case cs of
    [] -> return su
    ((t1, t2) : cs') -> do
      su1 <- unifies t1 t2
      solver (su1 `compose` su, apply su1 cs')

bind :: TVar -> Type-> Solve Subst
bind a t | t == TVar a     = return emptySubst
         | occursCheck a t = throwError $ InfiniteType a t
         | otherwise       = return (Subst $ Map.singleton a t)

occursCheck :: Substitutable a => TVar -> a -> Bool
occursCheck a t = a `Set.member` ftv t
