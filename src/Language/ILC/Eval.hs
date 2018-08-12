{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Syntax
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Evaluating ILC expressions.
--
--------------------------------------------------------------------------------

module Language.ILC.Eval where

import Control.Concurrent
import Control.Exception
import Control.Monad
import Data.IORef
import Data.List
import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.Typeable
import Development.Placeholders

import Language.ILC.Syntax

data Value
    = VInt Integer
    | VBool Bool
    | VString String
    | VTag String
    | VList [Value]
    | VSet [Value]
    | VTuple [Value]
    | VUnit
    | VClosure (Maybe Name) TermEnv Expr
    | VThunk TermEnv Expr
    | VChannel Name (Chan Value)
    | VRef (IORef Value)
    deriving (Eq)

newtype EvalError
    = EvalError String
    deriving (Typeable)

instance Show EvalError where
    show (EvalError s) = "Exceptions: " ++ s
    
instance Exception EvalError

-- TODO: Use pp
instance Show Value where
    show (VInt n) = show n
    show (VBool b) | b         = "true"
                   | otherwise = "false"
    show (VString s) = show s
    show (VTag t) = show t
    show (VList vs) = show vs
    show (VSet vs) = show vs
    show (VTuple vs) = show vs
    show VUnit = show ()
    show VClosure {} = "<closure>" -- TODO
    show VThunk {} = "<thunk>"
    show (VChannel x _) = x
    show (VRef _) = "<ref>"

type TermEnv = Map.Map Name Value

emptyTmEnv :: TermEnv
emptyTmEnv = Map.empty

extendEnv :: TermEnv -> Name -> Value -> TermEnv
extendEnv env x v = Map.insert x v env

updateEnv :: TermEnv -> [(Name, Value)] -> TermEnv
updateEnv = foldl f
  where
    f env (x, v) = Map.insert x v env

evalSub :: TermEnv -> Expr -> IO Value
evalSub env e = newEmptyMVar >>= \m ->
                eval' env m e >>
                takeMVar m
                
evalSubs :: TermEnv -> Expr -> Expr -> IO (Value, Value)
evalSubs env e1 e2 = evalSub env e1 >>= \v1 ->
                     evalSub env e2 >>= \v2 ->
                     return (v1, v2)

evalBinOp :: ((Value, Value) -> IO Value)
          -> TermEnv
          -> MVar Value
          -> Expr
          -> Expr
          -> IO ()
evalBinOp f env m e1 e2 =
    evalSubs env e1 e2 >>= f >>= putMVar m
    
evalArith :: (Integer -> Integer -> Integer)
          -> TermEnv
          -> MVar Value
          -> Expr
          -> Expr
          -> IO ()
evalArith = evalBinOp . f
  where
    f op (VInt n1, VInt n2) = return $ VInt (op n1 n2)
    f _  _                  = error "Eval.evalArith"

evalBool :: (Bool -> Bool -> Bool) -> TermEnv -> MVar Value -> Expr -> Expr -> IO ()
evalBool = evalBinOp . f
  where
    f op (VBool b1, VBool b2) = return $ VBool (op b1 b2)
    f _  _                    = error "Eval.evalBool"

evalRel :: (Integer -> Integer -> Bool) -> TermEnv -> MVar Value -> Expr -> Expr -> IO ()
evalRel = evalBinOp . f
  where
    f op (VInt n1, VInt n2) = return $ VBool (op n1 n2)
    f _  _        = error "Eval.evalRel"

evalRelPoly :: (Value -> Value -> Bool) -> TermEnv -> MVar Value -> Expr -> Expr -> IO ()
evalRelPoly = evalBinOp . f
  where
    f op (n1, n2) = return $ VBool (op n1 n2)

evalList :: TermEnv -> MVar Value -> ([Value] -> Value) -> [Expr] -> IO ()
evalList env m con es = (con <$> mapM (evalSub env) es) >>= putMVar m

evalPatMatch :: TermEnv -> [(Pattern, Expr, Expr)] -> Value -> IO Value
evalPatMatch _ [] _ = error "pattern match failed"
evalPatMatch env ((p, g, e):bs) val =
    case getBinds p val of
        Just binds -> let env' = updateEnv env binds
                      in evalSub env' g >>=
                      \case
                          VBool True  -> evalSub env' e
                          VBool False -> evalPatMatch env bs val
                          _           -> error "Eval.evalPatMatch"
        Nothing    -> evalPatMatch env bs val

(<:>) :: Applicative f => f [a] -> f [a] -> f [a]
(<:>) a b = (++) <$> a <*> b

letBinds :: Pattern -> Value -> [(Name, Value)]
letBinds p v = fromMaybe (error "let pattern matching failed") $
               getBinds p v

-- TODO: cons pattern match not failing on let x:xs = "foo" in x               
getBinds :: Pattern -> Value -> Maybe [(Name, Value)]
getBinds = go []
  where
    go acc (PVar x) v= Just ((x, v) : acc)
    go acc (PInt n) (VInt n') | n == n'   = Just acc
                              | otherwise = Nothing
    go acc (PBool b) (VBool b') | b == b'   = Just acc
                                | otherwise = Nothing
    go acc (PString s) (VString s') | s == s'   = Just acc
                                    | otherwise = Nothing
    go acc (PTag t) (VTag t') | t == t'   = Just acc
                              | otherwise = Nothing
    go acc (PList ps) (VList vs) = gos acc ps vs
    go acc (PCons p ps) (VList (v:vs)) = foldl1 (<:>) [acc1, acc2, Just acc]
      where
        acc1 = getBinds p v
        acc2 = getBinds ps (VList vs)
    go _ (PCons _ _) (VList []) = Nothing
    -- TODO: Set pattern matching not implemented.
    go acc (PSet ps) (VSet vs) = gos acc ps vs
    go acc (PTuple ps) (VTuple vs) = gos acc ps vs
    go acc PUnit VUnit = Just acc
    go acc PWildcard _ = Just acc
    go _ p v = error ("pattern match failed on" ++ show p ++ show v)
    
    -- TODO: Refactor using concatMap?
    gos acc vs ps | length vs == length ps = foldl (<:>) (Just []) accs
                  | otherwise              = Nothing
      where
        accs  = map (\case (v, p) -> go acc v p) vp
        vp    = zip vs ps
        
eval :: TermEnv -> Expr -> IO Value
eval env e = newEmptyMVar >>= \v ->
             eval' env v e >>
             takeMVar v

eval' :: TermEnv -> MVar Value -> Expr -> IO ()
eval' env m expr = case expr of
    EVar x -> putMVar m $ env Map.! x
    EImpVar _ -> $(todo "Eval implicit variables")
    ELit (LInt n) -> putMVar m $ VInt n
    ELit (LBool b) -> putMVar m $ VBool b
    ELit (LString s) -> putMVar m $ VString s
    ELit (LTag t) -> putMVar m $ VTag t
    ELit LUnit -> putMVar m VUnit
    ETuple es -> evalList env m VTuple es
    EList es -> evalList env m VList es
    ESet es -> evalList env m VSet $ nub es  -- TODO: Use Set
    ELam p e -> putMVar m $ VClosure (f p) env e
      where
        f (PVar x) = Just x
        f _        = Nothing
    EApp e1 e2 -> evalSub env e1 >>= \v1 ->
                  evalSub env e2 >>=
                  evalApp v1     >>= putMVar m
      where
        evalApp (VClosure x venv e) v =
            case x of
                Just x' -> let env' = extendEnv venv x' v
                           in evalSub env' e
                Nothing -> evalSub env e
        evalApp _                  _ = error "Eval.eval': EApp"
    EFix e -> evalSub env e' >>= putMVar m
      where
        e' = ELam (PVar "_x") (EApp (EApp e (EFix e)) (EVar "_x"))
    ELet p e1 e2 -> evalSub env e1 >>= \v1 ->
                    let binds = letBinds p v1
                        env'  = updateEnv env binds
                    in evalSub env' e2 >>= putMVar m
    EIf e1 e2 e3 -> evalSub env e1 >>= evalBranch >>= putMVar m
      where
        evalBranch (VBool True)  = evalSub env e2
        evalBranch (VBool False) = evalSub env e3
        evalBranch _             = error "Eval.eval': EIf"
    EMatch e bs -> evalSub env e >>=
                   evalPatMatch env bs >>=
                   putMVar m
    ENu (rdc, wrc) e ->
        newChan >>= \c ->
        let env' = updateEnv env [f rdc, f wrc]
            f x  = (x, VChannel x c)
        in evalSub env' e >>= putMVar m
    ERd e -> evalSub env e >>= \c -> getChan c >>=
             readChan >>= \v ->
             putMVar m $ VTuple [v, c]
      where
        getChan (VChannel _ c) = return c
        getChan _              = error "Eval.eval': ERd"
    EWr e1 e2 -> evalSub env e2 >>= getChan >>= \c ->
                 evalSub env e1 >>= writeChan c >> putMVar m VUnit
      where
        getChan (VChannel _ c) = return c
        getChan _              = error "Eval.eval': EWr"
    EFork e1 e2 -> newEmptyMVar >>= \m1 ->
                   newEmptyMVar >>= \m2 ->
                   forkIO (eval' env m1 e1) >>
                   forkIO (eval' env m2 e2) >>
                   takeMVar m2 >>= putMVar m
    -- TODO: Refactor
    EChoice e1 e2 ->
        newEmptyMVar >>= \m' ->
        newEmptyMVar >>= \choice ->
        forkFinally (eval' env m' e1) (\_ -> putMVar choice True) >>= \t1 ->
        forkFinally (eval' env m' e2) (\_ -> putMVar choice False) >>= \t2 ->
        takeMVar choice >>= \isleft ->
        when isleft (killThread t2) >>
        unless isleft (killThread t1) >>
        takeMVar m' >>= putMVar m
    ERepl e -> newEmptyMVar >>= \m' ->
               forkIO (forever $ eval' env m' e) >>
               putMVar m VUnit
    ERef e -> (VRef <$> (evalSub env e >>= newIORef)) >>= putMVar m
    EDeref e -> evalSub env e >>= getRef >>= readIORef >>= putMVar m
      where
        getRef (VRef r) = return r
        getRef _        = error "Eval.eval': EDeref"
    EAssign x e -> getRef (env Map.! x) >>= \r ->
                   evalSub env e >>=
                   writeIORef r >> putMVar m VUnit
      where
        getRef (VRef r) = return r
        getRef _        = error "Eval.eval': EAssign"
    ESeq e1 e2 -> evalSub env e1 >> evalSub env e2 >>= putMVar m
    -- TODO: Refactor
    EBin Add e1 e2 -> evalArith (+) env m e1 e2
    EBin Sub e1 e2 -> evalArith (-) env m e1 e2
    EBin Mul e1 e2 -> evalArith (*) env m e1 e2
    EBin Div e1 e2 -> evalArith quot env m e1 e2
    EBin Mod e1 e2 -> evalArith mod env m e1 e2
    EBin And e1 e2 -> evalBool (&&) env m e1 e2
    EBin Or e1 e2 -> evalBool (||) env m e1 e2
    EBin Lt e1 e2 -> evalRel (<) env m e1 e2
    EBin Gt e1 e2 -> evalRel (>) env m e1 e2
    EBin Leq e1 e2 -> evalRel (<=) env m e1 e2
    EBin Geq e1 e2 -> evalRel (>=) env m e1 e2
    EBin Eql e1 e2 -> evalRelPoly (==) env m e1 e2
    EBin Neq e1 e2 -> evalRelPoly (/=) env m e1 e2
    EBin Cons e1 e2 ->
        evalSubs env e1 e2 >>=
        (\case (x, VList xs) -> return $ VList $ x:xs
               _             -> error "Eval.eval': EBin Cons") >>=
        putMVar m
    EBin Concat e1 e2 ->
        evalSubs env e1 e2 >>=
        (\case
            (VList xs, VList ys)     -> return $ VList $ xs ++ ys
            (VString xs, VString ys) -> return $ VString $ xs ++ ys
            _                        -> error "Eval.eval': Concat") >>=
        putMVar m
    EUn Not e -> evalSub env e >>= neg >>= putMVar m
      where
        neg (VBool b) = return $ VBool $ not b
        neg _         = error "Eval.eval': Not"
    EThunk e -> putMVar m $ VThunk env e
    EForce e -> evalSub env e >>= force >>= putMVar m
      where
        force (VThunk env' e') = evalSub env' e'
        force _                = error "Eval.eval': EForce"
    EPrint e -> evalSub env e >>= print >> putMVar m VUnit
    EError e -> evalSub env e >>= getString >>= throwIO . EvalError
      where getString (VString s) = return s
            getString _           = return "Eval.eval': EError"

-- TODO: Types    
exec :: [Decl] -> IO Value
exec = go emptyTmEnv
  where
    go _   []       = error "Eval.exec"
    go env [(_, e)] = eval env e
    go env ((x, e):rest) = eval env e >>= \v ->
                               let env' = extendEnv env x v
                               in go env' rest
    -- go env ((CTySig _ _):rest) = go env rest
