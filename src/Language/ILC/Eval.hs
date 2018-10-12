{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Syntax
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- ILC expression evaluators.
--
--------------------------------------------------------------------------------

module Language.ILC.Eval (
    eval
  , exec
  ) where

import Control.Concurrent
import Control.Exception
import Data.IORef
import qualified Data.Map.Strict as Map
import Data.Typeable
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Language.ILC.Decl
import Language.ILC.Match
import Language.ILC.Syntax
import Language.ILC.Value

-- | Set up interpreter in IO monad (for filling and taking from mvars).
type Interpreter t = IO t

-- | Evaluating EError throws EvalError
newtype EvalError = EvalError String deriving (Typeable)

instance Exception EvalError

instance Show EvalError where
  show (EvalError s) = "Exception: " ++ s

-- | Evaluates an expression to a value and puts it into the given MVar.
evalPut :: TermEnv -> MVar Value -> Expr -> Interpreter ()
evalPut env m expr = case expr of
  EVar x -> do
    let v = case Map.lookup x env of
              Just val -> val
              Nothing  -> error $ "evalPut: EVar: Unbound variable " ++ x
    putMVar m v
    
  ELit (LInt n)    -> putMVar m $ VInt n
  ELit (LBool b)   -> putMVar m $ VBool b
  ELit (LString s) -> putMVar m $ VString s
  ELit LUnit       -> putMVar m VUnit
  
  ETuple es -> do
    res <- evalList env es
    putMVar m $ VTuple res

  EList es -> do
    res <- evalList env es
    putMVar m $ VList res

  ESett es -> do
    res <- evalList env es
    putMVar m $ VSet res
  
  ELam p e -> putMVar m $ VClosure (f p) env e
    where
      f (PVar x) = Just x
      f _        = Nothing
      
  EApp e1 e2 -> do
    (v1, v2) <- evalSubs env e1 e2
    res <- betaReduce env v1 v2
    putMVar m res

  EFix e -> do
    -- TODO: Use de Bruijn indicies.
    res <- eval env $ ELam (PVar "_x") (EApp (EApp e (EFix e)) (EVar "_x"))
    putMVar m res
      
  ELet p e1 e2 -> do
    v1 <- eval env e1
    -- If binds is not strict, this can miss invalid (but unused)
    -- pattern matches (e.g., let 1 = 2 in ...).
    let !binds = letBinds p v1
    res <- eval (Map.union env binds) e2
    putMVar m res

  ELetBang p e1 e2 -> do
    v1 <- eval env e1
    -- If binds is not strict, this can miss invalid (but unused)
    -- pattern matches (e.g., let 1 = 2 in ...).
    let !binds = letBinds p v1
    res <- eval (Map.union env binds) e2
    putMVar m res

  EBang e -> do
    res <- eval env e
    putMVar m res

  ELetRd p e1 e2 -> do
    v1 <- eval env e1
    -- If binds is not strict, this can miss invalid (but unused)
    -- pattern matches (e.g., let 1 = 2 in ...).
    let !binds = letBinds p v1
    res <- eval (Map.union env binds) e2
    putMVar m res
                  
  EIf e1 e2 e3 -> do
    v1 <- eval env e1
    res <- case v1 of
      VBool True  -> eval env e2
      VBool False -> eval env e3
      _           -> error "Eval.evalPut: EIf"
    putMVar m res

  EMatch e bs -> do
    v <- eval env e
    res <- evalMatch env v bs
    putMVar m res

  ENu (rdc, wrc) e -> do
    c <- newChan
    let env' = Map.union env $ Map.fromList [ (rdc, VRdChan rdc c)
                                            , (wrc, VWrChan wrc c)]
    res <- eval env' e
    putMVar m res

  ERd e -> do
    v <- eval env e
    let c = case v of
              VRdChan _ c' -> c'
              _            -> error "Eval.evalPut: ERd"
    res <- readChan c
    putMVar m $ VTuple [res, v]
      
  EWr e1 e2 -> do
    (v1, v2) <- evalSubs env e1 e2
    let c = case v2 of
              VWrChan _ c' -> c'
              _            -> error "Eval.evalPut: EWr"
    writeChan c v1
    putMVar m VUnit
      
  EFork e1 e2 -> do
    m1 <- newEmptyMVar
    m2 <- newEmptyMVar
    forkIO (evalPut env m1 e1)
    forkIO (evalPut env m2 e2)
    res <- takeMVar m2
    putMVar m res

  EChoice e1 e2 -> do
    m' <- newEmptyMVar
    forkIO (evalPut env m' e1)
    forkIO (evalPut env m' e2)
    res <- takeMVar m'
    putMVar m res

  ERef e -> do
    v <- eval env e
    ref <- newIORef v
    putMVar m $ VRef ref

  EGet e -> do
    v <- eval env e
    let r = case v of
              VRef r' -> r'
              _       -> error "Eval.evalPut: EGet"
    res <- readIORef r
    putMVar m res

  ESet x e -> do
    let r = case env Map.! x of
              VRef r' -> r'
              _       -> error "Eval.evalPut: ESet"
    v <- eval env e
    writeIORef r v
    putMVar m VUnit
      
  ESeq e1 e2 -> do
    (_, res) <- evalSubs env e1 e2
    putMVar m res

  EBin op e1 e2 -> do
    vs  <- evalSubs env e1 e2
    putMVar m $ evalBin op vs
      
  EUn Not e -> do
    v <- eval env e
    let res = case v of
                VBool b -> VBool $ not b
                _       -> error "Eval.evalPut: Not"
    putMVar m res
      
  EPrint e -> do
    v <- eval env e
    putDoc $ pretty v <> linebreak
    putMVar m VUnit
  
  EError e -> do
    v <- eval env e
    case v of
      VString s -> throwIO $ EvalError s
      _         -> error "Eval.evalPut: EError"

  ECustom x es -> do
    res <- evalList env es
    putMVar m $ VCust x res


-- | Evaluate two subexpressions                
evalSubs :: TermEnv -> Expr -> Expr -> Interpreter (Value, Value)
evalSubs env e1 e2 = do
  v1 <- eval env e1
  v2 <- eval env e2
  return (v1, v2)

evalBin :: Binop -> (Value, Value) -> Value
evalBin Add    = evalArith (+)
evalBin Sub    = evalArith (-)
evalBin Mul    = evalArith (*)
evalBin Div    = evalArith quot
evalBin Mod    = evalArith mod
evalBin And    = evalBool  (&&)
evalBin Or     = evalBool  (||)
evalBin Lt     = evalRel   (<)
evalBin Gt     = evalRel   (>)
evalBin Leq    = evalRel   (<=)
evalBin Geq    = evalRel   (>=)
evalBin Eql    = evalRelP  (==)
evalBin Neq    = evalRelP  (/=)
evalBin Cons   = evalCons
evalBin Concat = evalConcat

evalArith :: (Integer -> Integer -> Integer) -> (Value, Value) -> Value
evalArith op (VInt n1, VInt n2) = VInt (op n1 n2)
evalArith _  _                  = error "Eval.evalArith"

evalBool :: (Bool -> Bool -> Bool) -> (Value, Value) -> Value
evalBool op (VBool b1, VBool b2) = VBool (op b1 b2)
evalBool _  _                    = error "Eval.evalBool"

evalRel :: (Integer -> Integer -> Bool) -> (Value, Value) -> Value
evalRel op (VInt n1, VInt n2) = VBool (op n1 n2)
evalRel _  _                  = error "Eval.evalRel"

evalRelP :: (Value -> Value -> Bool) -> (Value, Value) -> Value
evalRelP op (v1, v2) = VBool (op v1 v2)

evalCons :: (Value, Value) -> Value
evalCons (v, VList vs) = VList $ v : vs
evalCons _             = error "Eval.evalCons"

evalConcat :: (Value, Value) -> Value
evalConcat (VList xs  , VList ys  ) = VList   $ xs ++ ys
evalConcat (VString xs, VString ys) = VString $ xs ++ ys
evalConcat _                        = error "Eval.evalConcat"

evalList :: TermEnv -> [Expr] -> Interpreter [Value]
evalList env = mapM $ eval env

betaReduce :: TermEnv -> Value -> Value -> IO Value
betaReduce env (VClosure m env' e) v =
  case m of
    Just x  -> eval (extendTmEnv env' x v) e
    Nothing -> eval env e
betaReduce _ _ _ = error "Eval.betaReduce"

-- | Evaluate pattern match branches
evalMatch :: TermEnv -> Value -> [(Pattern, Expr, Expr)] -> Interpreter Value
evalMatch _ _ [] = error "pattern match failed" -- TODO
evalMatch env val ((p, g, e):bs) =
  case runMatch p val of
    (Right _, binds) -> evalBranch (Map.union env binds)
    (Left  _, _)     -> evalMatch env val bs
  where
    evalBranch env' = do
      v <- eval env' g
      case v of
        VBool True  -> eval env' e
        VBool False -> evalMatch env val bs
        _           -> error "Eval.evalMatch"

-- | Evaluates an expression to a value
eval :: TermEnv -> Expr -> Interpreter Value
eval env e = do
  m <- newEmptyMVar
  evalPut env m e
  takeMVar m

-- | Evaluates a list of declarations to a value. The return value is the
-- evaluation of the last declaration in the list (i.e., the main function.)
exec :: [TopDecl] -> Interpreter Value
exec = go emptyTmEnv
  where
    go _   []                = error "Eval.exec"
    go env [(Decl _ e)]      = eval env e
    go env ((Decl x e):rest) = do v <- eval env e
                                  go (extendTmEnv env x v) rest
    go _ _                 = error "Eval.exec: Unimplemented"
