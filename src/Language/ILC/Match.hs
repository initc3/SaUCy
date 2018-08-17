--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Match
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Implements the Match monad for pattern matching. Returns either a MatchFail
-- or a list of variable bindings.
--
--------------------------------------------------------------------------------

module Language.ILC.Match (
    runMatch
  , MatchFail(..)
  , letBinds
  ) where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Writer
import Data.Map.Strict (fromList)
import Text.PrettyPrint.ANSI.Leijen

import Language.ILC.Syntax

type Match a = ExceptT MatchFail (WriterT TermEnv Identity) a

-- | Run the Match monad
runMatch :: Pattern -> Value -> (Either MatchFail (), TermEnv)
runMatch pat val =
  runIdentity (runWriterT (runExceptT (match pat val)))

-- | Failed pattern match
data MatchFail = MatchFail Pattern Value deriving (Show, Eq)

instance Pretty MatchFail where
  pretty (MatchFail pat val) = hsep [ text "Irrefutable pattern failed:"
                                    , text "could not match"
                                    , text "`" <> pretty pat <> text "`"
                                    , text "with"
                                    , text "`" <> pretty val <> text "`."
                                    ]

-- | Get variable bindings in pattern match
match :: Pattern -> Value -> Match ()
match (PVar x)     v                          = tell $ fromList [(x, v)]
match (PInt n)     (VInt n')    | n == n'     = return ()
match (PBool b)    (VBool b')   | b == b'     = return ()
match (PString s)  (VString s') | s == s'     = return ()
match (PTag t)     (VTag t')    | t == t'     = return ()
match (PTuple ps)  (VTuple vs)  | eqlen ps vs = zipWithM_ match ps vs
match (PList ps)   (VList vs)   | eqlen ps vs = zipWithM_ match ps vs
match (PCons p ps) (VList (v:vs))             = match p v >> match ps (VList vs)
match (PSet ps)    (VSet vs)    | eqlen ps vs = zipWithM_ match ps vs
match PUnit        VUnit                      = return ()
match PWildcard    _                          = return ()
match p            v                          = throwError $ MatchFail p v

eqlen :: [a] -> [b] -> Bool
eqlen l1 l2 = length l1 == length l2

-- | Returns variable bindings in a let binding.
-- This pattern match is irrefutable so this function
-- throws an error if it fails.
letBinds :: Pattern -> Value -> TermEnv
letBinds pat val = case runMatch pat val of
  (Left err, _)     -> error $ show $ pretty err
  (Right (), binds) -> binds
