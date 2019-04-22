--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Match
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Implements the @Match@ monad for pattern matching. 
--
--------------------------------------------------------------------------------

module Language.ILC.Match (
    Match
  , runMatch
  , MatchFail(..)
  , match
  , letBinds
  ) where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Writer
import Data.Map.Strict (fromList)
import Text.PrettyPrint.ANSI.Leijen

import Language.ILC.Decl
import Language.ILC.Syntax
import Language.ILC.Value

-- | The @Match@ monad returns either a @MatchFail@ error or a value of the
-- given type. It uses the @Writer@ monad to keep track of a list of variable
-- bindings (a term environment).
type Match a = ExceptT MatchFail (WriterT TermEnv Identity) a

-- | Runs the @Match@ monad on the given pattern and value.
runMatch :: Pattern -> Value -> (Either MatchFail (), TermEnv)
runMatch pat val =
  runIdentity (runWriterT (runExceptT (match pat val)))

-- | The error type of pattern match failures.
data MatchFail = MatchFail Pattern Value deriving (Show, Eq)

instance Pretty MatchFail where
  pretty (MatchFail pat val) = hsep [ text "Irrefutable pattern failed:"
                                    , text "could not match"
                                    , text "`" <> pretty pat <> text "`"
                                    , text "with"
                                    , text "`" <> pretty val <> text "`."
                                    ]

-- | Returns an instance of the @Match@ monad given a pattern and a value.
match :: Pattern -> Value -> Match ()
match (PVar x)     v                          = tell $ fromList [(x, v)]
match (PInt n)     (VInt n')    | n == n'     = return ()
match (PBool b)    (VBool b')   | b == b'     = return ()
match (PString s)  (VString s') | s == s'     = return ()
match (PTuple ps)  (VTuple vs)  | eqlen ps vs = zipWithM_ match ps vs
match (PList ps)   (VList vs)   | eqlen ps vs = zipWithM_ match ps vs
match (PCons p ps) (VList (v:vs))             = match p v >> match ps (VList vs)
match PUnit        VUnit                      = return ()
match PWildcard    _                          = return ()
match (PCust x ps) (VCust x' vs)| x == x'     = zipWithM_ match ps vs
match (PGnab p)    v                          = match p v
match p            v                          = throwError $ MatchFail p v

eqlen :: [a] -> [b] -> Bool
eqlen l1 l2 = length l1 == length l2

-- | Returns a term environment of variable bindings from a let binding. Pattern
-- matches in let expressions are irrefutable so this function will throw an
-- error if it fails.
letBinds :: Pattern -> Value -> TermEnv
letBinds pat val = case runMatch pat val of
  (Left err, _)     -> error $ show $ pretty err
  (Right (), binds) -> binds
