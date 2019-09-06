--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Pretty
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Pretty printing utility functions.
--
--------------------------------------------------------------------------------

module Language.ILC.Pretty (
    prettyTuple
  , _prettyTuple
  , prettySet
  , prettySpace
  , maybeParens
  ) where

import Data.List
import Text.PrettyPrint.ANSI.Leijen

-- | Pretty prints a comma separated list
-- TODO: Fix doc with to 80
prettyTuple :: [Doc] -> Doc
prettyTuple xs = encloseSep lparen rparen comma xs

-- | No line breaks
_prettyTuple :: Pretty a => [a] -> Doc
_prettyTuple xs = parens $ hcat $ intersperse comma $ map pretty xs

-- | Pretty prints a comma separated list
prettySet :: [Doc] -> Doc
prettySet xs = encloseSep lbrace rbrace comma xs

-- | Pretty prints a space separated list
prettySpace :: [Doc] -> Doc
prettySpace xs = encloseSep empty empty space xs

-- | Enclose a 'Doc' in parens if the flag is 'True'
maybeParens :: Bool -> Doc -> Doc
maybeParens True  = parens
maybeParens False = id
