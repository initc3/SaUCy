module Language.ILC.Util (
    prettyTuple
  , _prettyTuple
  , prettySet
  , maybeParens
  ) where

import Data.List
import Text.PrettyPrint.ANSI.Leijen

-- | Pretty prints a comma separated list
prettyTuple xs = encloseSep lparen rparen comma xs

-- | No line breaks
_prettyTuple xs = parens $ hcat $ intersperse comma $ map pretty xs

-- | Pretty prints a comma separated list
prettySet xs = encloseSep lbrace rbrace comma xs

-- | Pretty prints a space separated list
prettySpace xs = encloseSep empty empty space xs

-- | Enclose a 'Doc' in parens if the flag is 'True'
maybeParens :: Bool -> Doc -> Doc
maybeParens True  = parens
maybeParens False = id
