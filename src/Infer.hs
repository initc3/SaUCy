{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Infer where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Data.List (nub)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Development.Placeholders

import Syntax
import Type

--------------------------------------------------------------------------------
-- Classes
--------------------------------------------------------------------------------

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
    apply s (t1 `TArr` t2) = apply s t1 `TArr` apply s t2
    apply s (TList t) = TList (apply s t)
    apply s (TProd ts) = TProd (apply s ts)
    apply s (TSet t) = TSet (apply s t)
    apply s (TRef t) = TRef (apply s t)
    apply s (TThunk t) = TThunk (apply s t)
    apply s (TRdChan t) = TRdChan (apply s t)
    apply s (TWrChan t) = TWrChan (apply s t)

    ftv (TVar a) = Set.singleton a
    ftv TCon{} = Set.empty
    ftv (t1 `TArr` t2) = ftv t1 `Set.union` ftv t2
    ftv (TList t) = ftv t
    ftv (TProd ts) = ftv ts
    ftv (TSet t) = ftv t
    ftv (TRef t) = ftv t
    ftv (TThunk t) = ftv t
    ftv (TRdChan t) = ftv t
    ftv (TWrChan t) = ftv t

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

data TypeError
    = UnificationFail Type Type
    | InfiniteType TVar Type
    | UnboundVariable Name
    | Ambiguous [Constraint]
    | UnificationMismatch [Type] [Type]
    | ParFail Mode Mode
    | SeqFail Mode Mode
    | ChoiceFail Mode Mode

-- | Modes
parMode :: Mode -> Mode -> Infer Mode
parMode m1 m2 = case (m1, m2) of
    (MW, MV) -> return MW
    (MV, MW) -> return MW
    (MW, MR) -> return MW
    (MR, MW) -> return MW
    (MR, MR) -> return MR
    _        -> throwError $ ParFail m1 m2

seqMode :: Mode -> Mode -> Infer Mode
seqMode m1 m2 = case (m1, m2) of
    (MV, m)  -> return m
    (MW, MV) -> return MW
    (MR, _)  -> return MR
    (MW, MR) -> return MW
    _        -> throwError $ SeqFail m1 m2

choiceMode :: Mode -> Mode -> Infer Mode
choiceMode m1 m2 = case (m1, m2) of
    (MR, MR) -> return MR
    _        -> throwError $ ChoiceFail m1 m2

-------------------------------------------------------------------------------
-- Inference
-------------------------------------------------------------------------------

-- | Run the inference monad
runInfer :: TypeEnv -> Infer (Type, [Constraint], Mode) -> Either TypeError (Type, [Constraint], Mode)
runInfer env m = runExcept $ evalStateT (runReaderT m env) initInfer

-- | Solve for toplevel type of an expression in a give environment
inferExpr :: TypeEnv -> Expr -> Either TypeError (Scheme, Mode)
inferExpr env ex = case runInfer env (infer ex) of
    Left err       -> Left err
    Right (ty, cs, m) -> case runSolve cs of
        Left err    -> Left err
        Right subst -> Right (closeOver $ apply subst ty, m)

-- | Return internal constraints used in solving for type of expression
constraintsExpr :: TypeEnv -> Expr -> Either TypeError ([Constraint], Subst, Type, Scheme)
constraintsExpr env ex = case runInfer env (infer ex) of
    Left       err -> Left err
    Right (ty, cs, _) -> case runSolve cs of
        Left err    -> Left err
        Right subst -> Right (cs, subst, ty, sc)
          where sc = closeOver $ apply subst ty

closeOver :: Type-> Scheme
closeOver = normalize . generalize emptyTyEnv

inEnv :: (Name, (Scheme, Mode)) -> Infer a -> Infer a
inEnv (x, sc) m = do
    let scope e = remove e x `extend` (x, sc)
    local scope m

lookupEnv :: Name -> Infer (Type, Mode)
lookupEnv x = do
    (TypeEnv env) <- ask
    case Map.lookup x env of
        Nothing -> throwError $ UnboundVariable x
        Just (s, m)  -> do s' <- instantiate s
                           return (s', m)

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: Infer Type
fresh = do
    s <- get
    put s{count = count s + 1}
    return $ TVar $ TV (letters !! count s)

instantiate :: Scheme -> Infer Type
instantiate (Forall as t) = do
    as' <- mapM (const fresh) as
    let s = Subst $ Map.fromList $ zip as as'
    return $ apply s t

generalize :: TypeEnv -> Type-> Scheme -- ^ T-Gen
generalize env t = Forall as t
    where as = Set.toList $ ftv t `Set.difference` ftv env

abinops :: ABinop -> Infer Type
abinops Add = return $ tyInt  `TArr` (tyInt  `TArr` tyInt)
abinops Sub = return $ tyInt  `TArr` (tyInt  `TArr` tyInt)
abinops Mul = return $ tyInt  `TArr` (tyInt  `TArr` tyInt)
abinops Div = return $ tyInt  `TArr` (tyInt  `TArr` tyInt)
abinops Mod = return $ tyInt  `TArr` (tyInt  `TArr` tyInt)

bbinops :: BBinop -> Infer Type
bbinops And = return $ tyBool `TArr` (tyBool `TArr` tyBool)
bbinops Or  = return $ tyBool `TArr` (tyBool `TArr` tyBool)

rbinops :: RBinop -> Infer Type
rbinops Lt  = return $ tyInt  `TArr` (tyInt  `TArr` tyBool)
rbinops Gt  = return $ tyInt  `TArr` (tyInt  `TArr` tyBool)
rbinops Leq = return $ tyInt  `TArr` (tyInt  `TArr` tyBool)
rbinops Geq = return $ tyInt  `TArr` (tyInt  `TArr` tyBool)
rbinops Eql = eqbinop
rbinops Neq = eqbinop

eqbinop :: Infer Type
eqbinop = do
    t1 <- fresh
    t2 <- fresh
    return $ t1  `TArr` (t2  `TArr` tyBool)

bunops :: BUnop -> Type
bunops Not = tyBool  `TArr` tyBool

getBinds :: Pattern -> Expr -> [(Name, Expr)]
getBinds = go []
  where
    go acc (PVar x) e = (x, e) : acc
    go acc (PTuple ps) (ETuple es) = gos acc ps es
    go acc (PList ps) (EList es) = gos acc ps es
    go acc (PSet ps) (ESet es) = gos acc ps es
    go acc (PCons p ps) (EList (e:es)) = foldl1 (++) [acc1, acc2, acc]
      where
        acc1 = getBinds p e
        acc2 = getBinds ps (EList es)
    go acc _ _ = acc

    gos acc ps es | length ps == length es = accs
                  | otherwise              = error "pattern match fail"
      where
        accs  = concatMap (uncurry (go acc)) pe
        pe    = zip ps es

getPVars :: Pattern -> [Name]
getPVars = go []
  where
    go acc (PVar x) = x : acc
    go acc (PTuple ps) = concatMap getPVars ps ++ acc
    go acc (PList ps) = concatMap getPVars ps ++ acc
    go acc (PSet ps) = concatMap getPVars ps ++ acc
    go acc (PCons p ps) = foldl1 (++) [acc1, acc2, acc]
      where
        acc1 = getPVars p
        acc2 = getPVars ps
    go acc _ = acc

concatTCEs :: [(Type, [Constraint], [(Name, (Type, Mode))])]
           -> ([Type], [Constraint], [(Name, (Type, Mode))])
concatTCEs = foldr f ([], [], [])
  where
    f (t, c, e) (t', c', e') = (t : t', c ++ c', e ++ e')

concatTCs :: [(Type, [Constraint])]
           -> ([Type], [Constraint])
concatTCs = foldr f ([], [])
  where
    f (t, c) (t', c') = (t : t', c ++ c')

concatTCMs :: [(Type, [Constraint], Mode)]
           -> ([Type], [Constraint], [Mode])
concatTCMs = foldr f ([], [], [])
  where
    f (t, c, m) (t', c', m') = (t : t', c ++ c', m : m')

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
    thd <- fresh
    return $ if null ts then (thd, cs) else
                 (head ts, cs ++ map (\x -> (thd, x)) ts)
        
inferPat :: Pattern
         -> Maybe Expr
         -> Infer (Type, [Constraint], [(Name, (Type, Mode))])
inferPat pat expr = case (pat, expr) of
    (PVar x, Just e) -> do
        tv <- fresh
        (te, ce, m) <- infer e
        return (tv, (tv, te) : ce, [(x, (tv, m))])
    (PVar x, Nothing) -> do
        tv <- fresh
        return (tv, [], [(x, (tv, MV))])
        
    (PInt _, Just e) -> do
        (te, ce, _) <- infer e
        return (tyInt, (te, tyInt) : ce, [])
    (PInt _, Nothing) -> return (tyInt, [], [])
      
    (PBool _, Just e) -> do
        (te, ce, _) <- infer e
        return (tyBool, (te, tyBool) : ce, [])
    (PBool _, Nothing) -> return (tyBool, [], [])
      
    (PString _, Just e) -> do
        (te, ce, _) <- infer e
        return (tyString, (te, tyString) : ce, [])
    (PString _, Nothing) -> return (tyString, [], [])
      
    (PTag _, Just e) -> do
        (te, ce, _) <- infer e
        return (tyTag, (te, tyTag) : ce, [])
    (PTag _, Nothing) -> return (tyTag, [], [])

    (PTuple ps, Just (ETuple es)) -> do
        when (length ps /= length es) (error "fail") -- TODO: -- Custom error
        (tes, ces, _) <- infer $ ETuple es
        (ts, cs, env) <- inferPatList ps $ map Just es
        return (TProd ts, ces ++ cs ++ [(TProd ts, tes)], env)
    (PTuple ps, Just e) -> do
        (ts, cs, env) <- inferPatList ps $ repeat Nothing
        (te, ce, _) <- infer e
        return (TProd ts, cs ++ ce ++ [(TProd ts, te)], env)
    (PTuple ps, Nothing) -> do
        (ts, cs, env) <- inferPatList ps $ repeat Nothing
        return (TProd ts, cs, env)

    (PList ps, Just (EList es)) -> do
        when (length ps /= length es) (error "fail") -- TODO
        (tes, ces, _) <- infer $ EList es
        (ts, cs, env) <- inferPatList ps $ map Just es
        (thd, cs') <- listConstraints ts cs
        return (TList thd, ces ++ cs' ++ [(TList thd, tes)], env)
    (PList ps, Just e) -> do
        (te, ce, _) <- infer e
        (ts, cs, env) <- inferPatList ps $ repeat Nothing
        (thd, cs') <- listConstraints ts cs
        return (TList thd, ce ++ cs' ++ [(TList thd, te)], env)
    (PList ps, Nothing) -> do
        tces <- zipWithM inferPat ps $ repeat Nothing
        let (ts, cs, env) = concatTCEs tces
        (thd, cs') <- listConstraints ts cs
        return (TList thd, cs', env)

    (PSet ps, Just (ESet es)) -> do
        when (length ps /= length es) (error "fail") -- TODO
        (tes, ces, _) <- infer $ ESet es
        (ts, cs, env) <- inferPatList ps $ map Just es
        (thd, cs') <- listConstraints ts cs
        return (TSet thd, ces ++ cs' ++ [(TSet thd, tes)], env)
    (PSet ps, Just e) -> do
        (te, ce, _) <- infer e
        (ts, cs, env) <- inferPatList ps $ repeat Nothing
        (thd, cs') <- listConstraints ts cs
        return (TSet thd, ce ++ cs' ++ [(TSet thd, te)], env)
    (PSet ps, Nothing) -> do
        tces <- zipWithM inferPat ps $ repeat Nothing
        let (ts, cs, env) = concatTCEs tces
        (thd, cs') <- listConstraints ts cs
        return (TSet thd, cs', env)

    (PCons phd ptl, Just e@(EList (hd:tl))) -> do
        (te, ce, _) <- infer e
        (thd, chd, ehd) <- inferPat phd $ Just hd
        (ttl, ctl, etl) <- inferPat ptl $ Just $ EList tl
        let cs = ce ++ chd ++ ctl ++ [(te, TList thd), (te, ttl)]
            env = ehd ++ etl
        return (TList thd, cs, env)
    (PCons phd ptl, Just e) -> do
        (te, ce, _) <- infer e
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
        (te, ce, _) <- infer e
        return (tyUnit, ce ++ [(te, tyUnit)], [])
    (PUnit, Nothing) -> return (tyUnit, [], [])

    (PWildcard, Just _) -> do
        ty <- fresh
        return (ty, [], [])
    (PWildcard, Nothing) -> do
        ty <- fresh
        return (ty, [], [])

inferBranch :: Expr -> (Pattern, Expr, Expr) -> Infer (Type, [Constraint])
inferBranch expr (pat, pguard, branch) = do
    env <- ask
    (_, c1, env') <- inferPat pat $ Just expr
    case runSolve c1 of
        Left err -> throwError err
        Right sub -> do
            let sc t = generalize (apply sub env) (apply sub t)
            (t2, c2, _) <- foldr (\(x, (t, m)) -> inEnv (x, (sc t, m)))
                              (local (apply sub) (infer pguard))
                              env'
            (t3, c3, _) <- foldr (\(x, (t, m)) -> inEnv (x, (sc t, m)))
                              (local (apply sub) (infer branch))
                              env'
            return (t3, c1 ++ c2 ++ c3 ++ [(t2, tyBool)])

infer :: Expr -> Infer (Type, [Constraint], Mode)
infer expr = case expr of
    EVar x -> do
        (t, m) <- lookupEnv x
        return (t, [], m)

    EImpVar _ -> $(todo "Infer implicit variables")
        
    ELit (LInt _) -> return (tyInt, [], MV)
    ELit (LBool _) -> return (tyBool, [], MV)
    ELit (LString _) -> return (tyString, [], MV)
    ELit (LTag _) -> return (tyTag, [], MV)
    ELit LUnit -> return (tyUnit, [], MV)

    ETuple es -> do
        tcms <- mapM infer es
        let (ts, cs, _) = concatTCMs tcms
        -- TODO: Check all ms
        return (TProd ts, cs, MV)
        
    EList [] -> do
        tv <- fresh
        return (TList tv, [], MV)

    -- Refactor
    EList es -> do
        tcms <- mapM infer es
        let tyFst = (\(x, _, _) -> x) $ head tcms
            cs    = concatMap (\(_,x,_) -> x) tcms
            cs'   = map (\(x, _, _) -> (tyFst, x)) tcms
        return (TList tyFst, cs ++ cs', MV)

    ESet [] -> do
        ty <- fresh
        return (TSet ty, [], MV)
        
    ESet es -> do
        tcms <- mapM infer es
        let tyFst = (\(x, _, _) -> x) $ head tcms
            cs    = concatMap (\(_,x,_) -> x) tcms
            cs'   = map (\(x, _, _) -> (tyFst, x)) tcms
        return (TSet tyFst, cs ++ cs', MV)
    
    EBinArith op e1 e2 -> do
        (t1, c1, MV) <- infer e1
        (t2, c2, MV) <- infer e2
        tv <- fresh
        let u1 = t1 `TArr` (t2 `TArr` tv)
        u2 <- abinops op
        return (tv, c1 ++ c2 ++ [(u1, u2), (t1, t2)], MV)

    EBinBool op e1 e2 -> do
        (t1, c1, MV) <- infer e1
        (t2, c2, MV) <- infer e2
        tv <- fresh
        let u1 = t1 `TArr` (t2 `TArr` tv)
        u2 <- bbinops op
        return (tv, c1 ++ c2 ++ [(u1, u2), (t1, t2)], MV)
        
    EBinRel op e1 e2 -> do
        (t1, c1, MV) <- infer e1
        (t2, c2, MV) <- infer e2
        tv <- fresh
        let u1 = t1 `TArr` (t2 `TArr` tv)
        u2 <- rbinops op
        return (tv, c1 ++ c2 ++ [(u1, u2), (t1, t2)], MV)

    EUnBool op e -> do
        (t, c, MV) <- infer e
        tv <- fresh
        let u1 = t `TArr` tv
            u2 = bunops op
        return (tv, c ++ [(u1, u2)], MV)

    EIf e1 e2 e3 -> do
        (t1, c1, m1) <- infer e1
        (t2, c2, m2) <- infer e2
        (t3, c3, m3) <- infer e3
        when (m2 /= m3) (error "modes")
        m <- seqMode m1 m2
        return (t2, c1 ++ c2 ++ c3 ++ [(t1, tyBool), (t2, t3)], m)

    ELet p e1 e2 -> do
        env <- ask
        (t1, c1, env') <- inferPat p $ Just e1
        (_, _, m1) <- infer e1  -- TODO
        case runSolve c1 of
            Left err -> throwError err
            Right sub -> do
                let sc t = generalize (apply sub env) (apply sub t)
                (t2, c2, m2) <- foldr (\(x, (t, m)) -> inEnv (x, (sc t, m)))
                                  (local (apply sub) (infer e2))
                                  env'
                m <-  seqMode m1 m2
                return (t2, c1 ++ c2 ++ [(t1, t2)], m)

    EMatch e bs -> do
        tcs <- mapM (inferBranch e) bs
        let (ts, cs) = concatTCs tcs
            ty       = head ts
            cs'      = zip (tail ts) (repeat ty)
        return (ty, cs ++ cs', MV) -- TODO

    ELam (PVar x) e -> do
        ty <- fresh
        (t, c, m) <- inEnv (x, (Forall [] ty, MV)) (infer e)
        return (ty `TArr` t, c, m)

    ELam PUnit e -> do
        (t, c, m) <- infer e
        return (tyUnit `TArr` t, c, m)

    ELam PWildcard e -> do
        ty <- fresh
        (t, c, m) <- infer e
        return (ty `TArr` t, c, m)

    ELam _ _ -> error "Infer.infer"
        
    EFix e -> do
      (t, c, m) <- infer e
      tv <- fresh
      return (tv, c ++ [(tv `TArr` tv, t)], m)
        
    EApp e1 e2 -> do
        (t1, c1, m1) <- infer e1
        (t2, c2, MV) <- infer e2 -- TODO
        tv <- fresh
        return (tv, c1 ++ c2 ++ [(t1, t2 `TArr` tv)], m1)

    ERd e -> do
        (t, c, _) <- infer e -- TODO
        tv <- fresh
        return (TProd [tv, TRdChan tv], c ++ [(t, TRdChan tv)], MR)
    
    EWr e1 e2 -> do
        (t1, c1, _) <- infer e1 -- TODO
        (t2, c2, _) <- infer e2
        return (tyUnit, c1 ++ c2 ++ [(t2, TWrChan t1)], MW)
        
    ENu (rdc, wrc) e -> do
        tv <- fresh
        let newChans = [ (rdc, (Forall [] $ TRdChan tv, MV))
                       , (wrc, (Forall [] $ TWrChan tv, MV))]
        (t, c, m) <- foldr (\p a -> inEnv p a) (infer e) newChans
        return (t, c , m)

    ERepl e -> do
        (t, c, m) <- infer e
        return (t, c, m) -- TODO
    
    EFork e1 e2 -> do
        (_, c1, m1) <- infer e1
        (t2, c2, m2) <- infer e2
        m <- parMode m1 m2
        return (t2, c1 ++ c2, m)

    EChoice e1 e2 -> do
        (t1, c1, m1) <- infer e1 -- TODO
        (t2, c2, m2) <- infer e2
        m <- choiceMode m1 m2
        return (t1, c1 ++ c2 ++ [(t1, t2)], m)

    ESeq e1 e2 -> do
        (_, c1, m1) <- infer e1
        (t2, c2, m2) <- infer e2
        m <- seqMode m1 m2
        return (t2, c1 ++ c2, m)

    ERef e -> do
        (t, c, _) <- infer e
        tv <- fresh
        return (tv, c ++ [(tv, TRef t)], MV)

    EDeref e -> do
        (t, c, _) <- infer e
        tv <- fresh
        return (tv, c ++ [(TRef tv, t)], MV) -- TODO

    EAssign x e -> do
        (t1, _) <- lookupEnv x
        (t2, c2, _) <- infer e
        return (tyUnit, c2 ++ [(t1, TRef t2)], MV)

    EBin Cons e1 e2  -> do
       (t1, c1, MV) <- infer e1
       (t2, c2, MV) <- infer e2
       return (t2, c1 ++ c2 ++ [(TList t1, t2)], MV)

    EBin Concat e1 e2  -> do
       (t1, c1, MV) <- infer e1
       (t2, c2, MV) <- infer e2
       return (t1, c1 ++ c2 ++ [(t1, t2)], MV)

    EUn Thunk e -> do
        (t, c, _) <- infer e -- TODO
        tv <- fresh
        return (tv, c ++ [(tv, TThunk t)], MV)

    EUn Force e -> do
        (t, c, m) <- infer e
        tv <- fresh
        return (tv, c ++ [(TThunk tv, t)], m) -- TODO

    EUn Print e -> do
       (_, c, _) <- infer e
       return (tyUnit, c, MV)

    EUn Error e  -> do
       ty <- fresh
       (t, c, _) <- infer e
       return (ty, c ++ [(t, tyString)], MV)

inferTop :: TypeEnv -> [(Name, Expr)] -> Either TypeError TypeEnv
inferTop env [] = Right env
inferTop env ((name, ex):xs) = case inferExpr env ex of
    Left err -> Left err
    Right (ty, m) -> inferTop (extend env (name, (ty, m))) xs

normalize :: Scheme -> Scheme
normalize (Forall _ body) = Forall (map snd ord) (normtype body)
  where
    ord = zip (nub $ fv body) (map TV letters)

    fv (TVar a) = [a]
    fv (TArr a b) = fv a ++ fv b
    fv (TCon _) = []
    fv (TList a) = fv a
    -- TODO: Refactor?
    fv (TProd as) = concatMap fv as
    fv (TSet a) = fv a
    fv (TRef a) = fv a
    fv (TThunk a) = fv a
    fv (TRdChan a) = fv a
    fv (TWrChan a) = fv a
    
    normtype (TVar a)   =
        case Prelude.lookup a ord of
            Just x -> TVar x
            Nothing -> error "type variable not in signature"
    normtype (TCon a)   = TCon a
    normtype (TArr a b) = TArr (normtype a) (normtype b)
    normtype (TList a)   = TList (normtype a)
    normtype (TProd as)   = TProd (map normtype as)
    normtype (TSet a)   = TSet (normtype a)
    normtype (TRef a)   = TRef (normtype a)
    normtype (TThunk a)   = TThunk (normtype a)
    normtype (TRdChan a)   = TRdChan (normtype a)
    normtype (TWrChan a)   = TWrChan (normtype a)
    
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
unifies (TArr t1 t2) (TArr t3 t4) = unifyMany [t1, t2] [t3, t4]
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
