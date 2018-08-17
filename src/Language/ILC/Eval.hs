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
import Control.Monad
import Data.IORef
import Data.List
import qualified Data.Map.Strict as Map
import Data.Typeable
import Development.Placeholders
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Language.ILC.Match
import Language.ILC.Syntax

-- | Set up interpreter in IO monad (for filling and taking from mvars).
type Interpreter t = IO t

-- | Evaluating EError throws EvalError
newtype EvalError = EvalError String deriving (Typeable)

instance Exception EvalError

instance Show EvalError where
  show (EvalError s) = "Exception: " ++ s

-- | Evaluates an expression to a value and fills the mvar
eval' :: TermEnv -> MVar Value -> Expr -> Interpreter ()
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
      
  EApp e1 e2 -> do
    v1 <- eval env e1
    v2 <- eval env e2
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
                  
  EIf e1 e2 e3 -> do
    v1 <- eval env e1
    res <- case v1 of
      VBool True  -> eval env e2
      VBool False -> eval env e3
      _           -> error "Eval.eval': EIf"
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
              _           -> error "Eval.eval': ERd"
    res <- readChan c
    putMVar m $ VTuple [res, v]
      
  EWr e1 e2 -> do
    v1 <- eval env e1
    v2 <- eval env e2
    let c = case v2 of
              VWrChan _ c' -> c'
              _            -> error "Eval.eval': EWr"
    writeChan c v1
    putMVar m VUnit
      
  EFork e1 e2 -> do
    m1 <- newEmptyMVar
    m2 <- newEmptyMVar
    forkIO (eval' env m1 e1)
    forkIO (eval' env m2 e2)
    res <- takeMVar m2
    putMVar m res

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
    
  ERepl e -> do
    m' <- newEmptyMVar
    forkIO (forever $ eval' env m' e)
    putMVar m VUnit

  ERef e -> do
    v <- eval env e
    ref <- newIORef v
    putMVar m $ VRef ref

  EDeref e -> eval env e >>= getRef >>= readIORef >>= putMVar m
    where
      getRef (VRef r) = return r
      getRef _        = error "Eval.eval': EDeref"
  EAssign x e -> getRef (env Map.! x) >>= \r ->
                 eval env e >>=
                 writeIORef r >> putMVar m VUnit
    where
      getRef (VRef r) = return r
      getRef _        = error "Eval.eval': EAssign"
  ESeq e1 e2 -> eval env e1 >> eval env e2 >>= putMVar m
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
  EUn Not e -> eval env e >>= neg >>= putMVar m
    where
      neg (VBool b) = return $ VBool $ not b
      neg _         = error "Eval.eval': Not"
  EThunk e -> putMVar m $ VThunk env e
  EForce e -> eval env e >>= force >>= putMVar m
    where
      force (VThunk env' e') = eval env' e'
      force _                = error "Eval.eval': EForce"
  EPrint e -> eval env e >>= putDoc . pretty >> putMVar m VUnit
  EError e -> eval env e >>= getString >>= throwIO . EvalError
    where getString (VString s) = return s
          getString _           = error "Eval.eval': EError"

-- | Evaluate two subexpressions                
evalSubs :: TermEnv -> Expr -> Expr -> Interpreter (Value, Value)
evalSubs env e1 e2 = eval env e1 >>= \v1 ->
                     eval env e2 >>= \v2 ->
                     return (v1, v2)

evalBinOp :: ((Value, Value) -> Interpreter Value)
          -> TermEnv
          -> MVar Value
          -> Expr
          -> Expr
          -> Interpreter ()
evalBinOp f env m e1 e2 = evalSubs env e1 e2 >>= f >>= putMVar m

evalArith :: (Integer -> Integer -> Integer)
          -> TermEnv
          -> MVar Value
          -> Expr
          -> Expr
          -> Interpreter ()
evalArith = evalBinOp . f
  where
    f op (VInt n1, VInt n2) = return $ VInt (op n1 n2)
    f _  _                  = error "Eval.evalArith"

evalBool :: (Bool -> Bool -> Bool)
         -> TermEnv
         -> MVar Value
         -> Expr
         -> Expr
         -> Interpreter ()
evalBool = evalBinOp . f
  where
    f op (VBool b1, VBool b2) = return $ VBool (op b1 b2)
    f _  _                    = error "Eval.evalBool"

evalRel :: (Integer -> Integer -> Bool)
        -> TermEnv
        -> MVar Value
        -> Expr
        -> Expr
        -> Interpreter ()
evalRel = evalBinOp . f
  where
    f op (VInt n1, VInt n2) = return $ VBool (op n1 n2)
    f _  _        = error "Eval.evalRel"

evalRelPoly :: (Value -> Value -> Bool)
            -> TermEnv
            -> MVar Value
            -> Expr
            -> Expr
            -> Interpreter ()
evalRelPoly = evalBinOp . f
  where
    f op (n1, n2) = return $ VBool (op n1 n2)

evalList :: TermEnv
         -> MVar Value ->
         ([Value] -> Value)
         -> [Expr]
         -> Interpreter ()
evalList env m con es = (con <$> mapM (eval env) es) >>= putMVar m

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
      (Right _, binds) -> let env' = Map.union env binds
                    in eval env' g >>=
                    \case
                        VBool True  -> eval env' e
                        VBool False -> evalMatch env val bs
                        _           -> error "Eval.evalMatch"
      (Left _, _)    -> evalMatch env val bs

-- | Evaluates an expression to a value
eval :: TermEnv -> Expr -> Interpreter Value
eval env e = newEmptyMVar  >>= \v ->
             eval' env v e >>
             takeMVar v

-- | Evaluates a list of declarations to a value. The return value is the
-- evaluation of the last declaration in the list (i.e., the main function.)
exec :: [Decl] -> Interpreter Value
exec = go emptyTmEnv
  where
    go _   []            = error "Eval.exec"
    go env [(_, e)]      = eval env e
    go env ((x, e):rest) = eval env e >>= \v ->
                           let env' = extendTmEnv env x v
                           in go env' rest
