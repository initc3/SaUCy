{-# LANGUAGE TupleSections              #-}
{-# OPTIONS_GHC -Wall                   #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Infer.Infer
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Damas-Milner type inference for ILC programs.
--
--------------------------------------------------------------------------------

module Language.ILC.Infer.Infer (
    inferExpr
  , inferTop
  , closeOver
) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.List (nub)
import Debug.Trace

import Language.ILC.Infer.Solver
import Language.ILC.Syntax
import Language.ILC.Type
import Language.ILC.TypeError

import qualified Data.Map as Map
import qualified Data.Set as Set

-------------------------------------------------------------------------------
-- Inference
-------------------------------------------------------------------------------

-- | Inference monad
type Infer a = ReaderT TypeEnv (StateT InferState (Except TypeError)) a

-- | Inference state
newtype InferState = InferState { count :: Int }

-- | Initial inference state
initInfer :: InferState
initInfer = InferState { count = 0 }

-- | Run the inference monad
runInfer :: TypeEnv
         -> Infer (Type, [Constraint], TypeEnv)
         -> Either TypeError (Type, [Constraint], TypeEnv)
runInfer env m = runExcept $ evalStateT (runReaderT m env) initInfer

-- | Solve for type of toplevel expression in a given environment
inferExpr :: TypeEnv -> Expr -> Either TypeError Scheme
inferExpr env ex = case runInfer env (infer ex) of
  Left err          -> Left err
  Right (ty, cs, _) -> case runSolve cs of
    Left err    -> Left err
    Right subst -> Right (closeOver $ apply subst ty)

-- | Return internal constraints used in solving for type of expression
--constraintsExpr :: TypeEnv
--                -> Expr
--                -> Either TypeError ([Constraint], Subst, Type, Scheme)
--constraintsExpr env ex = case runInfer env (infer ex) of
--  Left       err -> Left err
--  Right (ty, cs, _) -> case runSolve cs of
--    Left err    -> Left err
--    Right subst -> Right (cs, subst, ty, sc)
--      where sc = closeOver $ apply subst ty

localc :: TypeEnv -> Infer a -> Infer a
localc env = local (const env)

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
    Nothing  -> throwError $ UnboundVariable x
    Just ty  -> instantiate ty

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: (String -> a) -> Infer a
fresh f = do
  s <- get
  put s{count = count s + 1}
  return $ f (letters !! count s)

freshi :: Infer Type
freshi = fresh (IType . IVar . TV)  

instantiate :: Scheme -> Infer Type
instantiate (Forall as t) = do
    as' <- mapM (const freshi) as
    let s = Subst $ Map.fromList $ zip as as'
    return $ apply s t

generalize :: TypeEnv -> Type-> Scheme -- ^ T-Gen
generalize env t = Forall as t
  where as = Set.toList $ ftv t `Set.difference` ftv env

binops :: Binop -> Infer Type
binops op = case op of
  Add ->  tyArithOp
  Sub -> tyArithOp
  Mul -> tyArithOp
  Div -> tyArithOp
  Mod -> tyArithOp
  And -> tyLogOp
  Or  -> tyLogOp
  Lt  -> tyRelOp
  Gt  -> tyRelOp
  Leq -> tyRelOp
  Geq -> tyRelOp
  Eql -> eqBinOp
  Neq -> eqBinOp
  _   -> error "Infer.binops"
  where
    tyArithOp = return $ IType (IArr tyInt (IType (IArr tyInt (IType tyInt))))
    tyLogOp = return $ IType (IArr tyBool (IType (IArr tyBool (IType tyBool))))
    tyRelOp = return $ IType (IArr tyInt (IType (IArr tyInt (IType tyBool))))
    eqBinOp = do
      t1 <- fresh (IVar . TV)
      t2 <- fresh (IVar . TV)
      return $ IType (IArr t1 (IType (IArr t2 (IType tyBool))))        

unops :: Unop -> Type
unops Not = IType (IArr tyBool (IType tyBool))

concatTCEs :: [(Type, [Constraint], [(Name, Type)])]
           -> ([Type], [Constraint], [(Name, Type)])
concatTCEs = foldr f ([], [], [])
  where
    f (t, c, e) (t', c', e') = (t : t', c ++ c', e ++ e')

concatTCEnvs :: [(Type, [Constraint], TypeEnv)]
           -> ([Type], [Constraint], TypeEnv)
concatTCEnvs = foldr f ([], [], emptyTyEnv)
  where
    f (t, c, e) (t', c', e') = (t : t', c ++ c', mergeTyEnv e e')    

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
  thd <- fresh (IVar . TV)
  return $ if null ts
           then (IType thd, cs)
           else (head ts, cs ++ map (IType thd,) ts)
        
inferPat :: Pattern
         -> Maybe Expr
         -> Infer (Type, [Constraint], [(Name, Type)])
inferPat pat expr = case (pat, expr) of
  (PVar x, Just e) -> do
    (ty, cs, _) <- infer e
    case ty of
      IType _ -> do
        tv <- freshi
        return (tv, (tv, ty) : cs, [(x, tv)])
      AType _ -> do
        tv <- fresh (AType . AVar . TV)
        return (tv, (tv, ty) : cs, [(x, tv)])
      UType _ -> error "todo"

  -- TODO: Universal type variable
  (PVar x, Nothing) -> do
    tv <- fresh (IVar . TV)
    return (IType tv, [], [(x, IType tv)])

  (PInt _, Just e) -> do
    (te, ce, _) <- infer e
    let constraints = (te, IType tyInt) : ce
    return (IType tyInt, constraints, [])
  (PInt _, Nothing) -> return (IType tyInt, [], [])

  (PBool _, Just e) -> do
    (te, ce, _) <- infer e
    let constraints = (te, IType tyBool) : ce
    return (IType tyBool, constraints, [])
  (PBool _, Nothing) -> return (IType tyBool, [], [])

  (PString _, Just e) -> do
    (te, ce, _) <- infer e
    let constraints = (te, IType tyString) : ce
    return (IType tyString, constraints, [])
  (PString _, Nothing) -> return (IType tyString, [], [])

  (PTuple ps, Just (ETuple es)) -> do
    when (length ps /= length es) (error "fail") -- TODO: -- Custom error
    (tes, ces, _) <- infer $ ETuple es
    case tes of
      IType _ -> do
        (ts, cs, ctxt) <- inferPatList ps $ map Just es
        let ts'         = map (\(IType x) -> x) ts
            constraints = (IType (IProd ts'), tes) : ces ++ cs
        return (IType (IProd ts'), constraints, ctxt)
      AType _ -> do
        (ts, cs, ctxt) <- inferPatList ps $ map Just es
        let ts'         = map (\(AType x) -> x) ts
            constraints = (AType (AProd ts'), tes) : ces ++ cs
        return (AType (AProd ts'), constraints, ctxt)
      UType _ -> error "todo"
  (PTuple [PGnab (PVar v), PVar c], Just e@(ERd _)) -> do
    tyS <- fresh (SVar . TV)
    (te, cs, _) <- infer e
    let tyR = AType (AProd [ABang . ISend $ tyS, ARdChan tyS])
    return (tyR, (tyR, te) : cs, [(v, IType . ISend $ tyS), (c, AType . ARdChan $ tyS)])
  (PTuple [PGnab p, PVar c], Just e@(ERd _)) -> do
    (_, _, binds) <- inferPat p Nothing
    tyS <- fresh (SVar . TV)
    (te, cs, _) <- infer e
    let tyR = AType (AProd [ABang . ISend $ tyS, ARdChan tyS])
    return (tyR, (tyR, te) : cs, (c, AType . ARdChan $ tyS) : binds)
  (PTuple ps, Just e) -> do
    (ts, cs, ctxt) <- inferPatList ps $ repeat Nothing
    (te, ce, _) <- infer e
    case te of
      IType _ -> do
        let ts' = map (\(IType x) -> x) ts            
        return (IType (IProd ts'), (IType (IProd ts'), te) : cs ++ ce, ctxt)
      AType _ -> do
        let ts' = map (\(AType x) -> x) (traceShow ts ts)
        return (AType (AProd ts'), (AType (AProd ts'), te) : cs ++ ce, ctxt)
      UType _ -> error "todo"
  (PTuple ps, Nothing) -> do
    (ts, cs, ctxt) <- inferPatList ps $ repeat Nothing
    case head ts of
      IType _ -> do
        let ts' = map (\(IType x) -> x) ts        
        return (IType (IProd ts'), cs, ctxt)
      AType _ -> do
        let ts' = map (\(AType x) -> x) ts        
        return (AType (AProd ts'), cs, ctxt)
      UType _ -> error "todo"

  (PList ps, Just (EList es)) -> do
    when (length ps /= length es) (error "fail") -- TODO
    (tes, ces, _) <- infer $ EList es
    (ts, cs, env) <- inferPatList ps $ map Just es
    (thd, cs') <- listConstraints ts cs
    let constraints = (IType (IList ((\(IType x) -> x) thd)), tes) : ces ++ cs'
    return (IType (IList ((\(IType x) -> x) thd)), constraints, env)
  (PList ps, Just e) -> do
    (te, ce, _) <- infer e
    (ts, cs, env) <- inferPatList ps $ repeat Nothing
    (thd, cs') <- listConstraints ts cs
    let constraints = (IType (IList ((\(IType x) -> x) thd)), te) : ce ++ cs'
    return (IType (IList ((\(IType x) -> x) thd)), constraints, env)
  (PList ps, Nothing) -> do
    tces <- zipWithM inferPat ps $ repeat Nothing
    let (ts, cs, env) = concatTCEs tces
    (thd, cs') <- listConstraints ts cs
    return (IType (IList ((\(IType x) -> x) thd)), cs', env)

  (PCons phd ptl, Just e@(EList (hd:tl))) -> do
    (te, ce, _) <- infer e
    (thd, chd, ehd) <- inferPat phd $ Just hd
    (ttl, ctl, etl) <- inferPat ptl $ Just $ EList tl
    let cs = ce ++ chd ++ ctl ++ [ (IType (IList ((\(IType x) -> x) thd)), te)
                                 , (te, ttl) ]
        env = ehd ++ etl
    return (IType (IList ((\(IType x) -> x) thd)), cs, env)
  (PCons phd ptl, Just e) -> do
    (te, ce, _) <- infer e
    (thd, chd, ehd) <- inferPat phd Nothing
    (ttl, ctl, etl) <- inferPat ptl Nothing
    let cs = ce ++ chd ++ ctl ++ [ (IType (IList ((\(IType x) -> x) thd)), te)
                                 , (te, ttl)
                                 , (IType (IList ((\(IType x) -> x) thd)), ttl) ]
        env = ehd ++ etl
    return (IType (IList ((\(IType x) -> x) thd)), cs, env)
  (PCons phd ptl, Nothing) -> do
    (thd, chd, ehd) <- inferPat phd Nothing
    (ttl, ctl, etl) <- inferPat ptl Nothing
    let cs = (IType (IList ((\(IType x) -> x) thd)), ttl) : chd ++ ctl
        env = ehd ++ etl
    return (IType (IList ((\(IType x) -> x) thd)), cs, env)

  (PUnit, Just e) -> do
    (ty, cs,  _) <- infer e
    return (IType tyUnit, (ty, IType tyUnit) : cs, [])
  (PUnit, Nothing) -> return (IType tyUnit, [], [])

  (PWildcard, _) -> do
    tv <- freshi
    return (tv, [], [])

  (PCust x ps, Just (ECustom x' es)) -> do
    tyx <- lookupEnv x
    let tyx' = typeSumDeconstruction tyx ps
    when (length ps /= length es) (error "fail1") -- TODO
    when (x /= x') (error "fail2") -- TODO
    (_, cs, env) <- inferPatList ps $ map Just es
    return (tyx', cs, env)
  (PCust x ps, Just e) -> do
    tyx <- lookupEnv x
    let tyx' = typeSumDeconstruction tyx ps
    (te, ce, _) <- infer e
    (_, cs, env) <- inferPatList ps $ repeat Nothing
    let constraints = (tyx', te) : ce ++ cs
    return (tyx', constraints, env)
  (PCust x ps, Nothing) -> do
    tyx <- lookupEnv x
    let tyx' = typeSumDeconstruction tyx ps
    tces <- zipWithM inferPat ps $ repeat Nothing
    let (_, cs, env) = concatTCEs tces
    return (tyx', cs, env)

  (PGnab _, _) -> error "todo"

-- | This function computes the type of a deconstructed sum type. The type of a
-- value constructor should either be an arrow type leading to a custom type
-- constructor (in the non-nullary case) or simply the custom type constructor
-- itself (in the nullary case).
-- TODO: Error handling.
typeSumDeconstruction :: Type -> [Pattern] -> Type
typeSumDeconstruction (IType (IArr _ t)) (_:ps) = typeSumDeconstruction t ps
typeSumDeconstruction t            []     = t
typeSumDeconstruction _            _      = error "Infer:typeSumDeconstruction"

inferBranch :: Expr
            -> (Pattern, Expr, Expr)
            -> Infer (Type, [Constraint], TypeEnv)
inferBranch expr (pat, grd, branch) = do
  env <- ask
  (_, c1, binds) <- inferPat pat $ Just expr
  (_, _, _Γ2) <- infer expr
  case runSolve c1 of
    Left err -> throwError err
    Right sub -> do
      let sc t = generalize (apply sub env) (apply sub t)
      (t2, c2, _Γ3) <- localc _Γ2 (foldr (\(x, t) -> inEnv (x, sc t))
                        (local (apply sub) (infer grd))
                        binds)
      (t3, c3, _Γ4) <- localc _Γ3 (foldr (\(x, t) -> inEnv (x, sc t))
                        (local (apply sub) (infer branch))
                        binds)
      let _Γ4' = foldl (\_Γ (x, _) -> removeTyEnv _Γ x) _Γ4 binds
          cs = (t2, IType tyBool) : c1 ++ c2 ++ c3
      return (t3, cs, _Γ4')

-- | Infer types of expression list
infers :: ([Type], [Constraint], TypeEnv)
       -> [Expr]
       -> Infer ([Type], [Constraint], TypeEnv)
infers = foldM (\(tys, cs1, env1) e -> do
                   (ty, cs2, env2) <- localc env1 (infer e) 
                   return (tys ++ [ty], cs1 ++ cs2, env2))

-- | Infer type of expression
infer :: Expr -> Infer (Type, [Constraint], TypeEnv)
infer expr = case expr of
  EVar x -> do
    env1 <- ask    
    ty   <- lookupEnv x
    let env2 = case ty of
          IType _ -> env1
          AType _ -> removeTyEnv env1 x
          UType _ -> error "todo"
    return (ty, [], env2)

  ELit lit -> do
    let ty = case lit of
               LInt{}    -> tyInt
               LBool{}   -> tyBool
               LString{} -> tyString
               LUnit     -> tyUnit
    asks (IType ty, [],)
    
  ETuple es -> do
    env1 <- ask
    (tys, cons, env2) <- infers ([],[],env1) es
    -- TODO: Check all unrestricted or all affine
    let ty = case head tys of
               IType _ -> IType . IProd . map  (\(IType x) -> x) $ tys
               AType _ -> AType . AProd . map  (\(AType x) -> x) $ tys
               UType _ -> error "todo"
    return (ty, cons, env2)

  EList [] -> do
    ty <- fresh (IType . IList . IVar . TV)
    asks (ty, [],)

  EList es -> do
    env1 <- ask
    (tys, cons1, env2) <- infers ([],[],env1) es
    let ty    = (\(IType x) -> x) (head tys)
        cons2 = map (IType ty,) tys
    return (IType . IList $ ty, cons1 ++ cons2, env2)

  EBin Cons e1 e2  -> do
   (IType tyA, cons1, env2) <- infer e1
   (tyAs, cons2, env3)      <- localc env2 (infer e2)
   return (tyAs, (IType (IList tyA), tyAs) : cons1 ++ cons2, env3)

  EBin Concat e1 e2  -> do
   (tyA, cons1, env2) <- infer e1
   (tyB, cons2, env3) <- localc env2 (infer e2)
   return (tyA, (tyA, tyB) : cons1 ++ cons2, env3)
   
  EBin op e1 e2 -> do
    (IType tyA, cs1, ctxt2) <- infer e1
    (IType tyB, cs2, ctxt3) <- localc ctxt2 (infer e2)
    tv <- freshi
    let u1 = IType (IArr tyA (IType (IArr tyB tv)))
    u2 <- binops op
    let cs = cs1 ++ cs2 ++ [(u1, u2), (IType tyA, IType tyB)]
    return (tv, cs, ctxt3)       

  EUn op e -> do
    (IType tyA, cons, env2) <- infer e
    tv <- freshi
    return (tv, (IType (IArr tyA tv), unops op) : cons, env2)

  -- TODO
  ELet p e1 e2 -> do
    ctxt1 <- ask
    (_, cs1, binds) <- inferPat p $ Just e1
    (_, cs2, ctxt2) <- infer e1
    case runSolve cs1 of
      Left err -> throwError err
      Right sub -> do
        let sc t   = generalize (apply sub ctxt1) (apply sub t)
            binds' = TypeEnv $ Map.fromList $ map (\(x, t) -> (x, sc t)) binds
            ctxt2' = apply sub (mergeTyEnv ctxt2 binds')
        (tyU, cs3, ctxt3) <- localc ctxt2' (infer e2)
        return (tyU, cs1 ++ cs2 ++ cs3, ctxt3)

  EBang e -> do
    (IType tyA, cons, env2) <- infer e
    return (AType (ABang tyA), cons, env2)

  EIf e1 e2 e3 -> do
    (tyA, cons1, env2) <- infer e1
    (tyB, cons2, env3) <- localc env2 (infer e2)
    (tyB', cons2', env3') <- localc env2 (infer e3)
    let cons = cons1 ++ cons2 ++ cons2' ++ [(tyA, IType tyBool), (tyB, tyB')]
    return (tyB, cons, intersectTyEnv env3 env3')    

  -- TODO
  EMatch e bs -> do
    tcmes <- mapM (inferBranch e) bs
    let (tys, cs, ctxts) = concatTCEnvs tcmes
        ty       = head tys
        cs'      = map (ty,) (tail tys)
    return (ty, cs ++ cs', ctxts)

  ELam p e ->
    case p of
      PVar x -> do
        ty <- fresh (IVar . TV)
        (tyU, cs, ctxt2) <- inEnv (x, Forall [] (IType ty)) (local clearAffineTyEnv (infer e))
        return (IType (ty `IArr` tyU), cs, ctxt2)
      PUnit -> do
        (tyU, cs, ctxt2) <- local clearAffineTyEnv $ infer e
        return (IType (tyUnit `IArr` tyU), cs, ctxt2)
      PWildcard -> do
        ty <- fresh (IVar . TV)
        (tyU, cs, ctxt2) <- local clearAffineTyEnv $ infer e        
        return (IType (ty `IArr` tyU), cs, ctxt2)
      _ -> error "Infer.infer: ELam"

  ELamw p e ->
    case p of
      PVar x -> do
        ty <- fresh (IVar . TV)
        (tyU, cs, ctxt2) <- inEnv (x, Forall [] (IType ty))
                            (inEnv ("WrTok", Forall [] (IType tyUnit))
                            (local clearAffineTyEnv (infer e)))
        return (IType (ty `IArrW` tyU), cs, ctxt2)
      PUnit -> do
        (tyU, cs, ctxt2) <- inEnv ("WrTok", Forall [] (IType tyUnit))      
                            (local clearAffineTyEnv (infer e))                
        return (IType (tyUnit `IArrW` tyU), cs, ctxt2)
      PWildcard -> do
        ty <- fresh (IVar . TV)
        (tyU, cs, ctxt2) <- inEnv ("WrTok", Forall [] (IType tyUnit))        
                            (local clearAffineTyEnv (infer e))                        
        return (IType (ty `IArrW` tyU), cs, ctxt2)
      _ -> error "Infer.infer: ELamW"      

  ELam1 p e ->
    case p of
      PVar x -> do
        ty <- fresh (AVar . TV)
        (tyU, cs, ctxt2) <- inEnv (x, Forall [] (AType ty)) (infer e)
        return (AType (ty `AArr` tyU), cs, ctxt2)
        -- TODO
--      PUnit -> do
--        (tyU, cs, ctxt2) <- infer e
--        return (IType (tyUnit `IArr` tyU), cs, ctxt2)
      PWildcard -> do
        ty <- fresh (AVar . TV)
        (tyU, cs, ctxt2) <- infer e        
        return (AType (ty `AArr` tyU), cs, ctxt2)
      _ -> error "Infer.infer: ELam1"

  EFix x e -> do
    ty <- fresh (IVar . TV)    
    (tyA2U, cs, ctxt2) <- inEnv (x, Forall [] (IType ty)) (infer e)
    return (tyA2U, (IType ty, tyA2U) : cs, ctxt2)

  EApp e1 e2 -> do
    (tyU1, cs1, ctxt2) <- infer e2
    (tyU12U2, cs2, ctxt3) <- localc ctxt2 (infer e1)
    case (tyU1, tyU12U2) of            
      (IType tyA1, IType (IArr tyA2 tyU2)) ->
        return (tyU2, cs1 ++ cs2 ++ [(IType tyA1, IType tyA2)], ctxt3)
      (IType tyA1, IType (IArrW tyA2 tyU2)) ->
        return (tyU2, cs1 ++ cs2 ++ [(IType tyA1, IType tyA2)], ctxt3)
      (AType tyX1, AType (AArr tyX2 tyU2)) ->
        return (tyU2, cs1 ++ cs2 ++ [(AType tyX1, AType tyX2)], ctxt3)
      (IType tyA1, IType tyA12U2) -> do
        tyU2 <- fresh (UType . UVar . TV)        
        return (tyU2, cs1 ++ cs2 ++ [(IType tyA12U2, IType (IArr tyA1 tyU2))], ctxt3)
      (IType tyA1, UType tv) -> do
        tyU2 <- fresh (UType . UVar . TV)        
        return (tyU2, cs1 ++ cs2 ++ [(UType tv, IType (IArr tyA1 tyU2))], ctxt3)                        
      (AType tyA1, AType tyA12U2) -> do
        tyU2 <- fresh (UType . UVar . TV)        
        return (tyU2, cs1 ++ cs2 ++ [(AType tyA12U2, AType (AArr tyA1 tyU2))], ctxt3)
      (AType tyA1, UType tv) -> do
        tyU2 <- fresh (UType . UVar . TV)        
        return (tyU2, cs1 ++ cs2 ++ [(UType tv, AType (AArr tyA1 tyU2))], ctxt3)                
      _ -> error (show (tyU1, tyU12U2, cs1 ++ cs2))

  ERd e -> do
    (AType tyRdS, cs, ctxt2) <- infer e
    tv <- fresh (SVar . TV)
    return (AType (AProd [ABang (ISend tv),tyRdS]), (AType tyRdS, AType (ARdChan tv)): cs, ctxt2)

  ELetRd p e1 e2 -> do
    ctxt1 <- ask
    when (checkWrTok ctxt1) (throwError WrTokenInRd)
    (_, cs1, binds) <- inferPat p $ Just e1
    (_, cs2, ctxt2) <- infer e1
    case runSolve cs1 of
      Left err -> throwError err
      Right sub -> do
        let sc t   = generalize (apply sub ctxt1) (apply sub t)
            binds' = TypeEnv $ Map.fromList $ map (\(x, t) -> (x, sc t)) binds
            ctxt2' = apply sub (mergeTyEnv ctxt2 binds')
            ctxt2'' = extendTyEnv ctxt2' ("WrTok", Forall [] (IType tyUnit))
        (tyU, cs3, ctxt3) <- localc ctxt2'' (infer e2)
        return (tyU, cs1 ++ cs2 ++ cs3, ctxt3)

  -- End TODO

  EWr e1 e2 -> do
    env1 <- ask
    unless (checkWrTok env1) (throwError NoWrTok)
    -- TODO: Check sendable
    (IType (ISend tyS), cons1, env2) <- local rmWrTok (infer e1)
    (tyWrS, cons2, env3) <- localc env2 (infer e2)
    return (IType tyUnit, (IType (IWrChan tyS), tyWrS) : cons1 ++ cons2, env3)
    
  ENu (rdc, wrc) e -> do
    tyS <- fresh (SVar . TV)
    let newChans = [ (rdc, Forall [] $ AType (ARdChan tyS))
                   , (wrc, Forall [] $ IType (IWrChan tyS))]
    (tyU, cons, env2) <- foldr inEnv (infer e) newChans
    return (tyU, cons, env2)
    
  EFork e1 e2 -> do
    (_, cons1, env2)   <- infer e1
    (tyU, cons2, env3) <- localc env2 (infer e2)
    return (tyU, cons1 ++ cons2, env3)

  -- TODO: Update choice
  EChoice e1 e2 -> do
    ctxt1 <- ask
    when (checkWrTok ctxt1) (throwError WrTokenInChoice)    
    (tyU1, cs1, ctxt2) <- infer e1
    (tyU2, cs2, ctxt3) <- infer e2
    return (tyU1, (tyU1, tyU2) : cs1 ++ cs2, intersectTyEnv ctxt2 ctxt3)

  EPrint e -> do
    (_, cons, env) <- infer e
    return (IType tyUnit, cons, env)

  -- TODO: Universal type variable
  EError e  -> do
    tv <- fresh (IType . IVar . TV)
    (IType _, cons, env) <- infer e
    return (tv, cons, env)

  ECustom x es -> do
    env1 <- ask
    ty <- lookupEnv x
    (_, _, env2) <- infers ([],[],env1) es
    return (ty, [], env2)

inferTop :: TypeEnv -> [(Name, Expr)] -> Either TypeError TypeEnv
inferTop env [] = Right env
inferTop env ((name, ex):xs) = case inferExpr env ex of
  Left err -> Left err
  Right ty -> inferTop (extendTyEnv env (name, ty)) xs

normalize :: Scheme -> Scheme
normalize (Forall _ body) = Forall (map snd ord) (normtype body)
  where
    ord = zip (nub $ fv body) (map TV letters)

    fv (IType a) = fvi a
    fv (AType a) = fva a
    fv (UType a) = fvu a

    fvu (UVar a)   = [a]
    fvu (UIType a) = fvi a
    fvu (UAType a) = fva a    

    fvi (IVar a)    = [a]
    fvi (ICon _)    = []
    fvi (IProd as)  = concatMap fvi as    
    fvi (IArr a b)  = fvi a ++ fv b
    fvi (IArrW a b) = fvi a ++ fv b    
    fvi (IList a)   = fvi a
    fvi (IWrChan a) = fvs a
    fvi (ICust a)   = fvi a
    fvi (ISend a)   = fvs a

    fva (AVar a)    = [a]
    fva (ARdChan a) = fvs a
    fva (AProd as)  = concatMap fva as
    fva (ABang a)   = fvi a
    fva (AArr a b)  = fva a ++ fv b    

    fvs (SVar a)   = [a]
    fvs (SProd as) = concatMap fvs as
    fvs (SCon _)   = []

    normtype (IType a) = IType (normtypei a)
    normtype (AType a) = AType (normtypea a)
    normtype (UType (UVar a))   = case Prelude.lookup a ord of
                                    Just x -> IType (IVar x)
                                    Nothing -> error "type variable not in signature"
    normtype (UType (UIType a)) = IType (normtypei a)
    normtype (UType (UAType a)) = AType (normtypea a)
    
    normtypei (IVar a)    = case Prelude.lookup a ord of
                              Just x -> IVar x
                              Nothing -> error "type variable not in signature"
    normtypei (ICon a)    = ICon a
    normtypei (IProd as)  = IProd (map normtypei as)    
    normtypei (IArr a b)  = IArr (normtypei a) (normtype b)
    normtypei (IArrW a b) = IArrW (normtypei a) (normtype b)    
    normtypei (IList a)   = IList (normtypei a)
    normtypei (IWrChan a) = IWrChan (normtypes a)
    normtypei (ICust a)   = ICust (normtypei a)
    normtypei (ISend a)   = ISend (normtypes a)

    normtypea (AVar a)    = case Prelude.lookup a ord of
                              Just x -> AVar x
                              Nothing -> error "type variable not in signature"
    normtypea (AProd as)  = AProd (map normtypea as)
    normtypea (ABang a)   = ABang (normtypei a)    
    normtypea (ARdChan a) = ARdChan (normtypes a)
    normtypea (AArr a b)  = AArr (normtypea a) (normtype b)    

    normtypes (SVar a)   = case Prelude.lookup a ord of
                             Just x -> SVar x
                             Nothing -> error "type variable not in signature"
    normtypes (SProd as) = SProd (map normtypes as)                
    normtypes (SCon a)   = SCon a
