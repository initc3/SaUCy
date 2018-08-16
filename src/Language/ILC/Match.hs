--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Match
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Returns MatchFail or variable bindings in a pattern match.
--
--------------------------------------------------------------------------------

module Language.ILC.Match (
      runMatch
    , MatchFail(..)
    ) where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Writer

import Language.ILC.Syntax

type Match a = ExceptT MatchFail (WriterT [(Name, Value)] Identity) a

-- | Run the match monad
runMatch :: Pattern -> Value -> (Either MatchFail (), [(Name, Value)])
runMatch pat val =
    runIdentity (runWriterT (runExceptT (match pat val)))

data MatchFail = MatchFail Pattern Value deriving (Show, Eq)

match :: Pattern -> Value -> Match ()
match (PVar x) v = tell [(x, v)]
match (PInt n) (VInt n') | n == n' = return ()
match (PBool b) (VBool b') | b == b' = return ()
match (PString s) (VString s') | s == s' = return ()
match (PTag t) (VTag t') | t == t' = return ()
match (PTuple ps) (VTuple vs) | eqlen ps vs = zipWithM_ match ps vs
match (PList ps) (VList vs) | eqlen ps vs = zipWithM_ match ps vs
match (PCons p ps) (VList (v:vs)) = match p v >> match ps (VList vs)
match (PSet ps) (VSet vs) | eqlen ps vs= zipWithM_ match ps vs
match PUnit VUnit = return ()
match PWildcard _ = return ()
match p v = throwError $ MatchFail p v

eqlen :: [a] -> [b] -> Bool
eqlen l1 l2 = length l1 == length l2
