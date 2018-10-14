{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE FlexibleInstances          #-}
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
  , closeOver
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

import Language.ILC.Mode
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
      
-- | Constraint solver monad
type Solve a = ExceptT TypeError Identity a

newtype Subst = Subst (Map.Map TVar TML)
  deriving (Eq, Ord, Show, Monoid)

class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set.Set TVar

instance Substitutable Type where
  apply _ (TCon a) = TCon a
  apply (Subst s) t@(TVar a) = case Map.findWithDefault (T t) a s of
    T ty -> ty
    _    -> t
  apply s (TArr t1 t2 m) = TArr (apply s t1) (apply s t2) (apply s m)
  apply s (TList t) = TList (apply s t)
  apply s (TProd ts) = TProd (apply s ts)
  apply s (TSet t) = TSet (apply s t)
  apply s (TRef t) = TRef (apply s t)
  apply s (TWrChan t) = TWrChan (apply s t)
  apply s (TLin l) = TLin (apply s l)
  apply s (TCust t) = TCust (apply s t)
  apply s TUsed = TUsed

  ftv (TVar a) = Set.singleton a
  ftv TCon{} = Set.empty
  ftv (TArr t1 t2 m) = ftv t1 `Set.union` ftv t2 `Set.union` ftv m
  ftv (TList t) = ftv t
  ftv (TProd ts) = ftv ts
  ftv (TSet t) = ftv t
  ftv (TRef t) = ftv t
  ftv (TWrChan t) = ftv t
  ftv (TLin l) = ftv l
  ftv (TCust t) = ftv t
  ftv TUsed = Set.empty

instance Substitutable LType where
  apply (Subst s) t@(LVar a) = case Map.findWithDefault (L t) a s of
    L ty -> ty
    _    -> t
  apply s (LRdChan t) = LRdChan (apply s t)
  apply s (LArr t1 t2 m) = LArr (apply s t1) (apply s t2) (apply s m)
  apply s (LTensor t1 t2) = LTensor (apply s t1) (apply s t2)
  apply s (LBang t) = LBang (apply s t)
  
  ftv (LVar a) = Set.singleton a
  ftv (LRdChan t) = ftv t
  ftv (LArr t1 t2 m) = ftv t1 `Set.union` ftv t2 `Set.union` ftv m
  ftv (LTensor t1 t2) = ftv t1 `Set.union` ftv t2
  ftv (LBang t) = ftv t

instance Substitutable Mode where
  apply (Subst s) m@(MVar a) = case Map.findWithDefault (M m) a s of
    M mo -> mo
    _    -> m
  apply s (MSeq m1 m2) = MSeq (apply s m1) (apply s m2)
  apply s (MPar m1 m2) = MPar (apply s m1) (apply s m2)
  apply _         m          = m

  ftv (MVar a) = Set.singleton a
  ftv (MSeq m1 m2) = ftv m1 `Set.union` ftv m2
  ftv (MPar m1 m2) = ftv m1 `Set.union` ftv m2
  ftv m        = Set.empty

instance Substitutable TML where
  apply s (T t) = T $ apply s t
  apply s (M m) = M $ apply s m
  apply s (L l) = L $ apply s l

  ftv (T t) = ftv t
  ftv (M m) = ftv m
  ftv (L l) = ftv l

instance Substitutable Scheme where
  apply (Subst s) (Forall as t) = Forall as $ apply s' t
    where s' = Subst $ foldr Map.delete s as
  ftv (Forall as t) = ftv t `Set.difference` Set.fromList as

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

checkType :: Eq a => a -> a -> String -> Infer a
checkType ty1 ty2 msg = if ty1 == ty2 then return ty1
                        else throwError (TypeFail msg)

-------------------------------------------------------------------------------
-- Inference
-------------------------------------------------------------------------------

-- | Run the inference monad
runInfer :: TypeEnv
         -> Infer (Type, [Constraint], Mode, TypeEnv)
         -> Either TypeError (Type, [Constraint], Mode, TypeEnv)
runInfer env m = runExcept $ evalStateT (runReaderT m env) initInfer

-- | Solve for type of top-level expression in a given environment
inferExpr :: TypeEnv -> Expr -> Either TypeError Scheme
inferExpr env ex = case runInfer env (infer ex) of
  Left err       -> Left err
  Right (ty, cs, m, _) -> case runSolve cs of
    Left err    -> Left err
    Right subst -> Right (closeOver $ simpFully $ apply subst ty)

-- | Return internal constraints used in solving for type of expression
constraintsExpr :: TypeEnv
                -> Expr
                -> Either TypeError ([Constraint], Subst, Type, Scheme)
constraintsExpr env ex = case runInfer env (infer ex) of
  Left       err -> Left err
  Right (ty, cs, _, _) -> case runSolve cs of
    Left err    -> Left err
    Right subst -> Right (cs, subst, ty, sc)
      where sc = closeOver $ apply subst ty

closeOver :: Type -> Scheme
closeOver = normalize . generalize emptyTyEnv

inEnv :: (Name, Scheme) -> Infer a -> Infer a
inEnv (x, sc) m = do
  let scope e = removeTyEnv e x `extendTyEnv` (x, sc)
  local scope m

lookupEnv :: Name -> Infer Type
lookupEnv x = do
  TypeEnv env <- ask
  case Map.lookup x env of
    Nothing -> throwError $ UnboundVariable x
    Just tyA  -> instantiate tyA

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: (String -> a) -> Infer a
fresh f = do
  s <- get
  put s{count = count s + 1}
  return $ f (letters !! count s)

freshifym :: Map.Map TVar TVar -> Mode -> Infer (Mode, Map.Map TVar TVar)
freshifym env V = return (V, env)
freshifym env R = return (R, env)
freshifym env W = return (W, env)
freshifym env (MVar a) = case Map.lookup a env of
  Nothing -> do
    b <- fresh TV
    return (MVar b, Map.insert a b env)
  Just b -> return (MVar b, env)
freshifym env (MSeq m1 m2) = do
  (m1', env1) <- freshifym env m1
  (m2', env2) <- freshifym env m2
  return (MSeq m1' m2', env2)
freshifym env (MPar m1 m2) = do
  (m1', env1) <- freshifym env m1
  (m2', env2) <- freshifym env m2
  return (MPar m1' m2', env2)

freshifyt :: Map.Map TVar TVar -> Type -> Infer (Type, Map.Map TVar TVar)
freshifyt env t@(TVar _) = return (t, env)
freshifyt env t@(TCon _) = return (t, env)
freshifyt env (TArr t1 t2 m) = do
  (t1', env1) <- freshifyt env t1
  (t2', env2) <- freshifyt env1 t2
  (m', env3)  <- freshifym env2 m
  return (TArr t1' t2' m', env3)
freshifyt env (TList t) = do
  (t', env') <- freshifyt env t
  return (TList t', env')
freshifyt env (TProd ts) = do
  (TProd ts', env') <- foldM (\(TProd acc, e) t -> (freshifyt e t) >>=
                       \(t', e') -> return (TProd (t':acc), e)) (TProd [], env) ts
  return (TProd (reverse ts'), env')
freshifyt env (TSet t) = do
  (t', env') <- freshifyt env t
  return (TSet t', env')
freshifyt env (TRef t) = do
  (t', env') <- freshifyt env t
  return (TRef t', env')
freshifyt env (TWrChan t) = do
  (t', env') <- freshifyt env t
  return (TWrChan t', env')
freshifyt env (TLin l) = do
  (l', env') <- freshifyl env l
  return (TLin l', env')
freshifyt env TUsed = return (TUsed, env)
freshifyt _ _ = error "Infer.freshifyt"

freshifyl :: Map.Map TVar TVar -> LType -> Infer (LType, Map.Map TVar TVar)
freshifyl env t@(LVar _) = return (t, env)
freshifyl env (LRdChan t) = do
  (t', env') <- freshifyt env t
  return (LRdChan t', env')
freshifyl env (LArr l1 l2 m) = do
  (l1', env1) <- freshifyl env l1
  (l2', env2) <- freshifyl env1 l2
  (m' , env3) <- freshifym env2 m
  return (LArr l1' l2' m', env3)
freshifyl env (LBang t) = do
  (t', env') <- freshifyt env t
  return (LBang t', env')

instantiate :: Scheme -> Infer Type
instantiate (Forall as t) = do
  as' <- mapM (const (fresh (TVar . TV))) as
  let s = Subst $ Map.fromList $ zip as (map T as')
      s' = apply s t
  (s'', _) <- freshifyt Map.empty s'
  return s''

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

concatTCEs :: [(Type, [Constraint], [(Name, Type)])]
           -> ([Type], [Constraint], [(Name, Type)])
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

concatTCMEs :: [(Type, [Constraint], Mode, TypeEnv)]
            -> ([Type], [Constraint], [Mode], [TypeEnv])
concatTCMEs = foldr f ([], [], [], [])
  where
    f (t, c, m, e) (t', c', m', e') = (t : t', c ++ c', m : m', e : e')

inferPatList :: [Pattern]
             -> [Maybe Expr]
             -> Infer ([Type], [Constraint], [(Name, Type)])
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
         -> Infer (Type, [Constraint], [(Name, Type)])
inferPat pat expr = case (pat, expr) of
  (PVar x, Just e) -> do
    tv <- fresh (TVar . TV)
    (te, ce, m, _) <- infer e
    let constraints = TypeConstraint tv te : ce
    return (tv, constraints, [(x, tv)])
  (PVar x, Nothing) -> do
    tv <- fresh (TVar . TV)
    return (tv, [], [(x, tv)])

  (PInt _, Just e) -> do
    (te, ce, _, _) <- infer e
    let constraints = TypeConstraint te tyInt : ce
    return (tyInt, constraints, [])
  (PInt _, Nothing) -> return (tyInt, [], [])

  (PBool _, Just e) -> do
    (te, ce, _, _) <- infer e
    let constraints = TypeConstraint te tyBool : ce
    return (tyBool, constraints, [])
  (PBool _, Nothing) -> return (tyBool, [], [])

  (PString _, Just e) -> do
    (te, ce, _, _) <- infer e
    let constraints = TypeConstraint te tyString : ce
    return (tyString, constraints, [])
  (PString _, Nothing) -> return (tyString, [], [])

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
    tyx <- lookupEnv x
    let tyx' = typeSumDeconstruction tyx ps
    when (length ps /= length es) (error "fail1") -- TODO
    when (x /= x') (error "fail2") -- TODO
    (ts, cs, env) <- inferPatList ps $ map Just es
    return (tyx', cs, env)
  (PCust x ps, Just e) -> do
    tyx <- lookupEnv x
    let tyx' = typeSumDeconstruction tyx ps
    (te, ce, _, _) <- infer e
    (ts, cs, env) <- inferPatList ps $ repeat Nothing
    let constraints = TypeConstraint tyx' te : ce ++ cs
    return (tyx', constraints, env)
  (PCust x ps, Nothing) -> do
    tyx <- lookupEnv x
    let tyx' = typeSumDeconstruction tyx ps
    tces <- zipWithM inferPat ps $ repeat Nothing
    let (ts, cs, env) = concatTCEs tces
    return (tyx', cs, env)

-- | This function computes the type of a deconstructed sum type. The type of a
-- value constructor should either be an arrow type leading to a custom type
-- constructor (in the non-nullary case) or simply the custom type constructor
-- itself (in the nullary case).
-- TODO: Error handling.
typeSumDeconstruction :: Type -> [Pattern] -> Type
typeSumDeconstruction (TArr _ t _) (p:ps) = typeSumDeconstruction t ps
typeSumDeconstruction t            []     = t
typeSumDeconstruction _            _      = error "Infer:typeSumDeconstruction"

inferPatLin :: Pattern
         -> Maybe Expr
         -> Infer (Type, [Constraint], [(Name, Type)])
inferPatLin pat expr = case (pat, expr) of
  (PVar x, Just (EVar y)) -> do
    tyy <- lookupEnv y
    tyV <- fresh (TVar . TV)
    let tyBang = TLin (LBang tyV)
    return (tyy, [TypeConstraint tyy tyBang], [(x, tyV)])
    
  _ -> error "Infer:inferPatLin"

inferBranch :: Expr
            -> (Pattern, Expr, Expr)
            -> Infer (Type, [Constraint], Mode, TypeEnv)
inferBranch expr (pat, guard, branch) = do
  env <- ask
  (_, c1, binds) <- inferPat pat $ Just expr
  (_, _, _, _Γ2) <- infer expr
  case runSolve c1 of
    Left err -> throwError err
    Right sub -> do
      let sc t = generalize (apply sub env) (apply sub t)
      (t2, c2, m1, _Γ3) <- local (const _Γ2) (foldr (\(x, t) -> inEnv (x, sc t))
                        (local (apply sub) (infer guard))
                        binds)
      let moConstraints = ModeConstraint m1 V
      (t3, c3, m, _Γ4) <- local (const _Γ3) (foldr (\(x, t) -> inEnv (x, sc t))
                        (local (apply sub) (infer branch))
                        binds)
      let _Γ4' = foldl (\_Γ (x, _) -> removeTyEnv _Γ x) _Γ4 binds
          tyConstraints = TypeConstraint t2 tyBool :c1 ++ c2 ++ c3
          constraints = moConstraints : tyConstraints
      return (t3, constraints, m, _Γ4')

sameThings :: Eq a => [a] -> Either TypeError a
sameThings (m:ms) = if (all (m ==) ms) then Right m else Left (TypeFail "Not same things.")

infer :: Expr -> Infer (Type, [Constraint], Mode, TypeEnv)
infer expr = case expr of
  EVar x -> do
    tyA <- lookupEnv x
    _Γ1 <- ask
    _Γ2 <- case tyA of
          TLin (LRdChan _) -> return $ extendTyEnv _Γ1 (x, closeOver TUsed)
          TUsed     -> throwError $ LinearFail x
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
  
  ELit LUnit -> do
    _Γ <- ask
    return (tyUnit, [], V, _Γ)
    
  ETuple es -> do
    _Γ1 <- ask
    -- TODO: Combine into one pass
    -- TODO: Elements should be value mode
    (_, _, _, _Γn) <- foldM (\(_, _, _, _Γ) e -> local (const _Γ) (infer e))
                      (tyUnit, [], V, _Γ1)
                      es
    tcmes <- mapM infer es
    let (tys, cs, ms, _) = concatTCMEs tcmes
        moConstraints = map (ModeConstraint V) ms
        constraints = cs ++ moConstraints
    return (TProd tys, constraints, V, _Γn)

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
   let tyConstraints = TypeConstraint (TList tyA1) tyA2 : c1 ++ c2
       moConstraints = [ModeConstraint m1 V, ModeConstraint m2 V]
       constraints = tyConstraints ++ moConstraints
   return (tyA2, constraints, V, _Γ3)

  EBin Concat e1 e2  -> do
   (tyA1, c1, m1, _Γ2) <- infer e1
   (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
   let tyConstraints = TypeConstraint tyA1 tyA2 : c1 ++ c2
       moConstraints = [ModeConstraint m1 V, ModeConstraint m2 V]
       constraints = tyConstraints ++ moConstraints
   return (tyA1, constraints, V, _Γ3)

  EBin op e1 e2 -> do
    (tyA1, c1, m1, _Γ2) <- infer e1
    (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
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
    -- TODO
    _ <- checkType _Γ3 _Γ3' "Branches have different outgoing typing contexts."
    m3 <- fresh (MVar . TV)
    let tyConstraints = c1 ++ c2 ++ c3 ++ [ TypeConstraint tyA1 tyBool
                                        , TypeConstraint tyA2 tyA3 ]
        moConstraints = [ ModeConstraint m1 V
                        , ModeConstraint m2 m3
                        , ModeConstraint m2 m2' ]
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
        (tyB, c2, m2, _Γ3) <- local (const _Γ2) (foldr (\(x, t) -> inEnv (x, sc t))
                              (local (apply sub) (infer e2))
                              binds)
        m3 <- fresh (MVar . TV)
        let tyConstraints = c1 ++ c2
            moConstraints = [ModeConstraint (MSeq m1 m2) m3]
            constraints = tyConstraints ++ moConstraints
        return (tyB, constraints, m3, _Γ3)

  ELetBang p e1 e2 -> do
    env <- ask
    tyV <- fresh (TVar . TV)
    (_, c1, binds) <- inferPatLin p $ Just e1
    (tye1, _, m1, _Γ2) <- infer e1
    let c1' = TypeConstraint tye1 (TLin (LBang tyV)) : c1
    case runSolve c1' of
      Left err -> throwError err
      Right sub -> do
        let sc t = generalize (apply sub env) (apply sub t)
        (tyB, c2, m2, _Γ3) <- local (const _Γ2) (foldr (\(x, t) -> inEnv (x, sc t))
                              (local (apply sub) (infer e2))
                              binds)
        m3 <- fresh (MVar . TV)
        let tyConstraints = c1' ++ c2
            moConstraints = [ModeConstraint (MSeq m1 m2) m3]
            constraints = tyConstraints ++ moConstraints
        return (tyB, constraints, m3, _Γ3)

  EBang e -> do
    (tyA, c, m, _Γ2) <- infer e
    tyV <- fresh (TVar . TV)
    let tyConstraints = TypeConstraint tyV (TLin (LBang tyA)) : c
        moConstraints = [ModeConstraint m V]
        constraints = tyConstraints ++ moConstraints
    return (tyV, constraints, V, _Γ2)

  ELetRd (PTuple [PVar v, PVar c]) (ERd e1) e2 -> do
    env <- ask
    tyV <- fresh (TVar . TV)
    let binds = [(v, TLin (LBang tyV)), (c, TLin (LRdChan tyV))]
    (tye1, c1, m1, _Γ2) <- infer (ERd e1)
    let c1' = TypeConstraint (TLin (LTensor (LBang tyV) (LRdChan tyV))) tye1 : c1
    case runSolve c1' of
      Left err -> throwError err
      Right sub -> do
        let sc t = generalize (apply sub env) (apply sub t)
        (tyB, c2, m2, _Γ3) <- (local (const _Γ2) (foldr (\(x, t) -> inEnv (x, sc t))
                              (local (apply sub) (infer e2))
                              binds))
        m3 <- fresh (MVar . TV)
        let tyConstraints = c1' ++ c2
            moConstraints = [ModeConstraint (MSeq m1 m2) m3]
            constraints = tyConstraints ++ moConstraints
        return (tyB, constraints, m3, _Γ3)

  EMatch e bs -> do
    tcmes <- mapM (inferBranch e) bs
    let (ts, cs, ms, _Γs) = concatTCMEs tcmes
        ty       = head ts
        cs'      = map (`TypeConstraint` ty) (tail ts)
    -- TODO: Clean up
    let envs = map (\case {TypeEnv binds -> Map.filter (\x -> x == Forall []
    TUsed) binds}) _Γs
    _ <- case sameThings envs  of
             Left err -> throwError err
             Right _Γ  -> return _Γ
    let tyConstraints = cs ++ cs'
        moConstraints = map (ModeConstraint V) ms
        constraints = tyConstraints ++ moConstraints
    return (ty, constraints, V, head _Γs)

  ELam (PVar x) e -> do
    tyV <- fresh (TVar . TV)
    (tyA, c, m, _Γ2) <- inEnv (x, Forall [] tyV) (infer e)
    (tyV', tyA') <- case runSolve c of
             Left err -> throwError err
             Right sub -> return (apply sub tyV, apply sub tyA)
    case (tyV', tyA') of
      (TLin lV', TLin lA') ->
        return (TLin (LArr lV' lA' m), c, V, _Γ2)
      _                    ->
        return (TArr tyV' tyA' m, c, V, _Γ2)

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
    tyA2A' <- case runSolve c of
             Left err -> throwError err
             Right sub -> return $ apply sub tyA2A
    mV <- fresh (MVar . TV)
    (tyRes, tyConstraints) <- case tyA2A' of
      TLin l -> do
        tyV <- fresh (LVar . TV)
        return (TLin tyV, TypeConstraint tyA2A (TLin (LArr tyV tyV mV )) : c)
      _      -> do
        tyV <- fresh (TVar . TV)
        return (tyV, TypeConstraint tyA2A (TArr tyV tyV mV) : c)
    let moConstraints  = [ModeConstraint m V]
        constraints = tyConstraints ++ moConstraints
    return (tyRes, constraints, V, _Γ2)
    
  EApp e1 e2 -> do
    (tyA, c1, m1, _Γ2) <- infer e2
    (tyA2B, c2, m2, _Γ3) <- local (const _Γ2) (infer e1)
    (tyA2B', tyA') <- case runSolve (c1 ++ c2) of
             Left err -> throwError err
             Right sub -> return (apply sub tyA2B, apply sub tyA)
    mV <- fresh (MVar . TV)
    (tyRet, tyConstraints) <- case (tyA2B', tyA') of
          (t, TLin l) -> do
            tyV <- fresh (LVar . TV)
            tyA' <- fresh (LVar . TV)
            return (TLin tyV, TypeConstraint tyA2B (TLin (LArr tyA' tyV mV)) : TypeConstraint (TLin tyA') tyA : c1 ++ c2)
          (t1, t2)    -> do
            tyV <- fresh (TVar . TV)
            return  (tyV, TypeConstraint tyA2B (TArr tyA tyV mV) : c1 ++ c2)
    let moConstraints = [ModeConstraint  m1 V, ModeConstraint m2 V]
        constraints = tyConstraints ++ moConstraints
    return (tyRet, constraints, mV, _Γ3)

  ERd e -> do
    (tyA, c, m, _Γ2) <- infer e
    tyV <- fresh (TVar . TV)
    let tyConstraints = TypeConstraint tyA (TLin (LRdChan tyV)) : c
        moConstraints = [ModeConstraint m V]
        constraints = tyConstraints ++ moConstraints
    return (TLin (LTensor (LBang tyV) (LRdChan tyV)), constraints, R, _Γ2)

  EWr e1 e2 -> do
    (tyA1, c1, m1, _Γ2) <- infer e1
    (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
    let tyConstraints = TypeConstraint tyA2 (TWrChan tyA1) : c1 ++ c2
        moConstraints = [ModeConstraint m1 V, ModeConstraint m2 V]
        constraints = tyConstraints ++ moConstraints
    return (tyUnit, constraints, W, _Γ3)

  ENu (rdc, wrc) e -> do
    tyV <- fresh (TVar . TV)
    let newChans = [ (rdc, Forall [] $ TLin (LRdChan tyV))
                   , (wrc, Forall [] $ TWrChan tyV)]
    (tyA, c, m, _Γ2) <- foldr inEnv (infer e) newChans
    return (tyA, c , m, _Γ2)

  EFork e1 e2 -> do
    (_, c1, m1, _Γ2) <- infer e1
    (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
    m3 <- fresh (MVar . TV)
    let tyConstraints = c1 ++ c2
        moConstraints = [ModeConstraint (MPar m1 m2) m3]
        constraints = tyConstraints ++ moConstraints
    return (tyA2, constraints, m3, _Γ2)

  EChoice e1 e2 -> do
    (tyA1, c1, m1, _Γ2) <- infer e1
    (tyA2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
    let tyConstraints = TypeConstraint tyA1 tyA2 : c1 ++ c2
        moConstraints = [ModeConstraint m1 R, ModeConstraint m2 R]
        constraints = tyConstraints ++ moConstraints
    return (tyA1, constraints, R, _Γ3)

  ESeq e1 e2 -> do
    (_, c1, m1, _Γ2) <- infer e1
    (t2, c2, m2, _Γ3) <- local (const _Γ2) (infer e2)
    m3 <- fresh (MVar . TV)
    let tyConstraints = c1 ++ c2
        moConstraints = [ModeConstraint (MSeq m1 m2) m3]
        constraints = tyConstraints ++ moConstraints
    return (t2, constraints, m3, _Γ3)

  ERef e -> do
    (tyA, c, m, _Γ2) <- infer e
    tyV <- fresh (TVar . TV)
    let tyConstraints = TypeConstraint tyV (TRef tyA) : c
        moConstraints = [ModeConstraint m V]
        constraints = tyConstraints ++ moConstraints
    return (tyV, constraints, V, _Γ2)

  EGet e -> do
    (tyA, c, m, _Γ2) <- infer e
    tyV <- fresh (TVar . TV)
    let tyConstraints = TypeConstraint (TRef tyV) tyA : c
        moConstraints = [ModeConstraint m V]
        constraints = tyConstraints ++ moConstraints
    return (tyV, constraints, V, _Γ2)

  ESet x e -> do -- TODO: Change to ESet e1 e2
    tyA1 <- lookupEnv x
    (tyA2, c, m, _Γ2) <- infer e
    let tyConstraints = TypeConstraint tyA1 (TRef tyA2) : c
        moConstraints = [ModeConstraint m V]
        constraints = tyConstraints ++ moConstraints
    return (tyUnit, constraints, V, _Γ2)

  EPrint e -> do
    (_, c, m, _Γ2) <- infer e
    return (tyUnit, ModeConstraint m V : c, V, _Γ2)

  EError e  -> do
    tyV <- fresh (TVar . TV)
    (tyA, c, m, _Γ2) <- infer e
    let tyConstraints = TypeConstraint tyA tyString : c
        moConstraints = [ModeConstraint m V]
        constraints = tyConstraints ++ moConstraints
    return (tyV, constraints, V, _Γ2)

  ECustom x es -> do
    _Γ1 <- ask
    tyx <- lookupEnv x
    (_, _, _, _Γn) <- foldM (\(_, _, _, _Γ) e -> local (const _Γ) (infer e))
                      (tyUnit, [], V, _Γ1)
                      es
    tcmes <- mapM infer es
    let (tys, cs, ms, _) = concatTCMEs tcmes
        moConstraints = map (ModeConstraint V) ms
        constraints = moConstraints
    return (tyx, [], V, _Γn)

inferTop :: TypeEnv -> [(Name, Expr)] -> Either TypeError TypeEnv
inferTop env [] = Right env
inferTop env ((name, ex):xs) = case inferExpr env ex of
  Left err -> Left err
  Right ty -> inferTop (extendTyEnv env (name, ty)) xs

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
    fv (TWrChan a) = fv a
    fv (TLin l) = fvl l
    fv (TCust a) = fv a
    fv TUsed = []

    fvm (MVar a) = [a]
    fvm (MSeq m1 m2) = fvm m1 ++ fvm m2
    fvm (MPar m1 m2) = fvm m1 ++ fvm m2
    fvm m        = []
    
    fvl (LVar a) = [a]
    fvl (LRdChan a) = fv a
    fvl (LArr a b m) = fvl a ++ fvl b ++ fvm m
    fvl (LTensor a b) = fvl a ++ fvl b
    fvl (LBang a) = fv a
    
    normtype (TVar a)   =
        case Prelude.lookup a ord of
            Just x -> TVar x
            Nothing -> error "type variable not in signature"
    normtype (TCon a)   = TCon a
    normtype (TArr a b m) = TArr (normtype a) (normtype b) (normmode m)
    normtype (TList a)   = TList (normtype a)
    normtype (TProd as)   = TProd (map normtype as)
    normtype (TSet a)   = TSet (normtype a)
    normtype (TRef a)   = TRef (normtype a)
    normtype (TWrChan a)   = TWrChan (normtype a)
    normtype (TLin l)   = TLin (normlin l)
    normtype (TCust a)   = TCust (normtype a)
    normtype TUsed   = TUsed

    normmode (MVar a) =
        case Prelude.lookup a ord of
            Just x -> MVar x
            Nothing -> error "mode variable not in signature"
    normmode (MSeq m1 m2) = MSeq (normmode m1) (normmode m2)
    normmode (MPar m1 m2) = MPar (normmode m1) (normmode m2)
    normmode m        = m

    normlin (LVar a)   =
        case Prelude.lookup a ord of
            Just x -> LVar x
            Nothing -> error "ltype variable not in signature"
    normlin (LRdChan a)  = LRdChan (normtype a)
    normlin (LArr a b m) = LArr (normlin a) (normlin b) (normmode m)
    normlin (LTensor a b) = LTensor (normlin a) (normlin b)
    normlin (LBang a)    = LBang (normtype a)
    
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

unifyMany :: [TML] -> [TML] -> Solve Subst
unifyMany [] []  = return emptySubst
unifyMany (t1 : ts1) (t2 : ts2) =
  do su1 <- unifies t1 t2
     su2 <- unifyMany (apply su1 ts1) (apply su1 ts2)
     return (su2 `compose` su1)
unifyMany t1 t2 = throwError $ UnificationMismatch t1 t2

unifies :: TML -> TML -> Solve Subst
unifies t1 t2 | t1 == t2 = return emptySubst
unifies (T (TVar v)) (T t) = v `bind` T t
unifies (T t) (T (TVar v)) = v `bind` T t
unifies (T (TArr t1 t2 m1)) (T (TArr t3 t4 m2)) = unifyMany [T t1, T t2, M m1] [T t3, T t4, M m2]
unifies (T (TList t1)) (T (TList t2)) = unifies (T t1) (T t2)
unifies (T (TProd ts1)) (T (TProd ts2)) = unifyMany (map T ts1) (map T ts2)
unifies (T (TSet t1)) (T (TSet t2)) = unifies (T t1) (T t2)
unifies (T (TRef t1)) (T (TRef t2)) = unifies (T t1) (T t2)
unifies (T (TWrChan t1)) (T (TWrChan t2)) = unifies (T t1) (T t2)
unifies (T (TLin l1)) (T (TLin l2)) = unifies (L l1) (L l2)
unifies (T (TCust t1)) (T (TCust t2)) = unifies (T t1) (T t2)

unifies (L (LVar v)) (L t) = v `bind` L t
unifies (L t) (L (LVar v)) = v `bind` L t
unifies (L (LRdChan t1)) (L (LRdChan t2)) = unifies (T t1) (T t2)
unifies (L (LArr l1 l2 m1)) (L (LArr l3 l4 m2)) = unifyMany [L l1, L l2, M m1] [L l3, L l4, M m2]
unifies (L (LTensor l1 l2)) (L (LTensor l3 l4)) = unifyMany [L l1, L l2] [L l3, L l4]
unifies (L (LBang t1)) (L (LBang t2)) = unifies (T t1) (T t2)

unifies (M (MVar v)) (M t) = v `bind` M t
unifies (M t) (M (MVar v)) = v `bind` M t
unifies (M (MSeq m1 m2)) (M (MSeq m3 m4)) = unifyMany [M m1, M m2] [M m3, M m4]
unifies (M (MPar m1 m2)) (M (MPar m3 m4)) = unifyMany [M m1, M m2] [M m3, M m4]

unifies t1 t2 = throwError $ UnificationFail t1 t2

solver :: Unifier -> Solve Subst
solver (su, cs) =
  case cs of
    [] -> return su
    (TypeConstraint t1 t2 : cs') -> do
      (t1',t2') <- case (simpty t1, simpty t2) of
                     (Nothing, _) -> throwError $ TypeFail "type"
                     (_, Nothing) -> throwError $ TypeFail "type"
                     (Just a, Just b) -> return (a,b)
      su1 <- unifies (T t1') (T t2')
      solver (su1 `compose` su, apply su1 cs')
    (ModeConstraint m1 m2 : cs') -> do
      (m1',m2') <- case (mcompose m1, mcompose m2) of
                     (Nothing, _) -> throwError $ ModeFail m1 m2
                     (_, Nothing) -> throwError $ ModeFail m1 m2
                     (Just a, Just b) -> return (a,b)
      su1 <- unifies (M m1') (M m2')
      solver (su1 `compose` su, apply su1 cs')
         
bind :: TVar -> TML -> Solve Subst
bind a (T t) | t == TVar a     = return emptySubst
             | occursCheck a t = throwError $ InfiniteType a t
             | otherwise       = return (Subst $ Map.singleton a (T t))
bind a (M t) | t == MVar a     = return emptySubst
             | otherwise       = return (Subst $ Map.singleton a (M t))
bind a (L t) | t == LVar a     = return emptySubst
             | otherwise       = return (Subst $ Map.singleton a (L t))

occursCheck :: Substitutable a => TVar -> a -> Bool
occursCheck a t = a `Set.member` ftv t
