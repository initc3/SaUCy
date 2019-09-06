{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# OPTIONS_GHC -Wall                   #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Infer.Solver
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Constraint solver
--
--------------------------------------------------------------------------------

module Language.ILC.Infer.Solver (
    Constraint
  , Unifier
  , Solve
  , Subst(..)  
  , Substitutable(..)
  , runSolve
) where

import Control.Monad.Except
import Control.Monad.Identity

import Language.ILC.Type
import Language.ILC.TypeError

import qualified Data.Map as Map
import qualified Data.Set as Set

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
  apply s (IType t) = IType (apply s t)
  apply s (AType t) = AType (apply s t)
  apply s (UType t) = UType (apply s t)  

  ftv (IType t) = ftv t
  ftv (AType t) = ftv t
  ftv (UType t) = ftv t

instance Substitutable UType where
  apply (Subst s) t@(UVar a) = strip $ Map.findWithDefault (UType t) a s
    where
      strip (UType x) = x
      strip (AType x) = UAType x
      strip (IType x) = UIType x
  apply _ _ = error "todo"

  ftv (UVar a) = Set.singleton a
  ftv _ = error "todo"  

instance Substitutable IType where
  apply (Subst s) t@(IVar a) = strip $ Map.findWithDefault (IType t) a s
    where
      strip (IType x) = x
      strip _ = error "Tried to strip non-unrestricted type"            
  apply _ (ICon a) = ICon a
  apply s (IProd ts) = IProd (apply s ts)
  apply s (IArr t1 t2) = IArr (apply s t1) (apply s t2)
  apply s (IArrW t1 t2) = IArrW (apply s t1) (apply s t2)  
  apply s (IList t) = IList (apply s t)
  apply s (IWrChan t) = IWrChan (apply s t)
  apply s (ICust t) = ICust (apply s t)
  apply s (ISend t) = ISend (apply s t)  

  ftv (IVar a) = Set.singleton a
  ftv ICon{} = Set.empty
  ftv (IProd ts) = ftv ts  
  ftv (IArr t1 t2) = ftv t1 `Set.union` ftv t2
  ftv (IArrW t1 t2) = ftv t1 `Set.union` ftv t2  
  ftv (IList t) = ftv t
  ftv (IWrChan t) = ftv t
  ftv (ICust t) = ftv t
  ftv (ISend t) = ftv t  

instance Substitutable AType where
  apply (Subst s) t@(AVar a) = strip $ Map.findWithDefault (AType t) a s
    where
      strip (AType x) = x
      strip _ = error "Tried to strip non-affine type"      
  apply s (ARdChan t) = ARdChan (apply s t)  
  apply s (AProd ts) = AProd (apply s ts)
  apply s (ABang t) = ABang (apply s t)
  apply s (AArr t1 t2) = AArr (apply s t1) (apply s t2)  

  ftv (AVar a) = Set.singleton a
  ftv (ARdChan t) = ftv t  
  ftv (AProd ts) = ftv ts
  ftv (ABang t) = ftv t
  ftv (AArr t1 t2) = ftv t1 `Set.union` ftv t2  

instance Substitutable SType where
  apply (Subst s) t@(SVar a) = strip $ Map.findWithDefault (IType (ISend t)) a s
    where
      strip (IType (ISend x)) = x
      strip _ = error "Tried to strip unsendable type"
  apply s (SProd ts) = SProd (apply s ts)
  apply _ (SCon a) = SCon a  

  ftv (SVar a) = Set.singleton a
  ftv (SProd ts) = ftv ts
  ftv SCon{} = Set.empty  

instance Substitutable Scheme where
  apply (Subst s) (Forall as t) = Forall as $ apply s' t
    where s' = Subst $ foldr Map.delete s as
    
  ftv (Forall as t) = ftv t `Set.difference` Set.fromList as

instance Substitutable Constraint where
  apply s (t1, t2) = (apply s t1, apply s t2)
  
  ftv (t1, t2) = ftv t1 `Set.union` ftv t2

instance Substitutable a => Substitutable [a] where
  apply = fmap . apply

  ftv = foldr (Set.union . ftv) Set.empty

instance Substitutable TypeEnv where
  apply s (TypeEnv env) = TypeEnv $ Map.map (apply s) env
  
  ftv (TypeEnv env) = ftv $ Map.elems env

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

unifies :: Type -> Type -> Solve Subst
unifies t1 t2 | t1 == t2 = return emptySubst
unifies (IType t1) (IType t2) = unifiesi t1 t2
unifies (AType t1) (AType t2) = unifiesa t1 t2
unifies t1 (UType t2) = unifiesu t1 (UType t2)
unifies (UType t1) t2 = unifiesu (UType t1) t2
unifies t1 t2 = throwError $ UnificationFail t1 t2

unifiesu :: Type -> Type -> Solve Subst
unifiesu t (UType (UVar v)) = v `bindu` t
unifiesu (UType (UVar v)) t = v `bindu` t
unifiesu (UType (UAType t1)) (AType t2) = unifiesa t1 t2
unifiesu (AType t1) (UType (UAType t2)) = unifiesa t1 t2
unifiesu (UType (UIType t1)) (IType t2) = unifiesi t1 t2
unifiesu (IType t1) (UType (UIType t2)) = unifiesi t1 t2
unifiesu t1 t2 = throwError $ UnificationFail t1 t2

unifiesi :: IType -> IType -> Solve Subst
unifiesi t1 t2 | t1 == t2 = return emptySubst
unifiesi (IVar v) t = v `bindi` t
unifiesi t (IVar v) = v `bindi` t
unifiesi (IProd ts1) (IProd ts2) = unifyManyi ts1 ts2
unifiesi (IArr t1 t2) (IArr t3 t4) = do
  (Subst s1) <- unifiesi t1 t3
  (Subst s2) <- unifies t2 t4
  return $ Subst $ s1 `Map.union` s2
unifiesi (IArrW t1 t2) (IArrW t3 t4) = do
  (Subst s1) <- unifiesi t1 t3
  (Subst s2) <- unifies t2 t4
  return $ Subst $ s1 `Map.union` s2  
unifiesi (IList t1) (IList t2) = unifiesi t1 t2
unifiesi (IWrChan t1) (IWrChan t2) = unifiess t1 t2
unifiesi (ICust t1) (ICust t2) = unifiesi t1 t2
unifiesi (ISend t1) (ISend t2) = unifiess t1 t2
unifiesi t1 t2 = throwError $ UnificationFail (wrap t1) (wrap t2)
  where
    wrap = IType

unifiesa :: AType -> AType -> Solve Subst
unifiesa t1 t2 | t1 == t2 = return emptySubst
unifiesa (AVar v) t = v `binda` t
unifiesa t (AVar v) = v `binda` t
unifiesa (ARdChan t1) (ARdChan t2) = unifiess t1 t2
unifiesa (AProd ts1) (AProd ts2) = unifyManya ts1 ts2
unifiesa (ABang t1) (ABang t2) = unifiesi t1 t2
unifiesa (AArr t1 t2) (AArr t3 t4) = do
  (Subst s1) <- unifiesa t1 t3
  (Subst s2) <- unifies t2 t4
  return $ Subst $ s1 `Map.union` s2
unifiesa t1 t2 = throwError $ UnificationFail (wrap t1) (wrap t2)
  where
    wrap = AType  

unifiess :: SType -> SType -> Solve Subst
unifiess t1 t2 | t1 == t2 = return emptySubst
unifiess (SVar v) t = v `binds` t
unifiess t (SVar v) = v `binds` t
unifiess (SProd ts1) (SProd ts2) = unifyManys ts1 ts2
unifiess t1 t2 = throwError $ UnificationFail (wrap t1) (wrap t2)
  where
    wrap = IType . ISend

unifyManyi :: [IType] -> [IType] -> Solve Subst
unifyManyi [] []  = return emptySubst
unifyManyi (t1 : ts1) (t2 : ts2) =
  do su1 <- unifiesi t1 t2
     su2 <- unifyManyi (apply su1 ts1) (apply su1 ts2)
     return (su2 `compose` su1)
unifyManyi t1 t2 = throwError $ UnificationMismatch t1' t2'
  where
    t1' = map IType t1
    t2' = map IType t2

unifyManya :: [AType] -> [AType] -> Solve Subst
unifyManya [] []  = return emptySubst
unifyManya (t1 : ts1) (t2 : ts2) =
  do su1 <- unifiesa t1 t2
     su2 <- unifyManya (apply su1 ts1) (apply su1 ts2)
     return (su2 `compose` su1)
unifyManya t1 t2 = throwError $ UnificationMismatch t1' t2'
  where
    t1' = map AType t1
    t2' = map AType t2

unifyManys :: [SType] -> [SType] -> Solve Subst
unifyManys [] []  = return emptySubst
unifyManys (t1 : ts1) (t2 : ts2) =
  do su1 <- unifiess t1 t2
     su2 <- unifyManys (apply su1 ts1) (apply su1 ts2)
     return (su2 `compose` su1)
unifyManys t1 t2 = throwError $ UnificationMismatch t1' t2'
  where
    t1' = map (IType . ISend) t1
    t2' = map (IType . ISend) t2

solver :: Unifier -> Solve Subst
solver (su, cs) =
  case cs of
    [] -> return su
    ((t1, t2) : cs') -> do
      su1 <- unifies t1 t2
      solver (su1 `compose` su, apply su1 cs')

bindu :: TVar -> Type -> Solve Subst
bindu _ (UType _ ) = error "todo"
bindu a t | t == IType (IVar a)     = return emptySubst
          | t == AType (AVar a)     = return emptySubst
bindu a (IType t) | occursCheck a t = throwError $ InfiniteType a (IType t)
                  | otherwise       = return (Subst $ Map.singleton a (IType t))
bindu a (AType t) | occursCheck a t = throwError $ InfiniteType a (AType t)
                  | otherwise       = return (Subst $ Map.singleton a (AType t))                        

bindi :: TVar -> IType -> Solve Subst
bindi a t | t == IVar a     = return emptySubst
          | occursCheck a t = throwError $ InfiniteType a (IType t)
          | otherwise       = return (Subst $ Map.singleton a (IType t))

binda :: TVar -> AType -> Solve Subst
binda a t | t == AVar a     = return emptySubst
          | occursCheck a t = throwError $ InfiniteType a (AType t)
          | otherwise       = return (Subst $ Map.singleton a (AType t))

binds :: TVar -> SType -> Solve Subst
binds a t | t == SVar a     = return emptySubst
          | occursCheck a t = throwError $ InfiniteType a (IType (ISend t))
          | otherwise       = return (Subst $ Map.singleton a (IType (ISend t)))          

occursCheck :: Substitutable a => TVar -> a -> Bool
occursCheck a t = a `Set.member` ftv t
