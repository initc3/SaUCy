{-# OPTIONS_GHC -Wall #-}
------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Parser.Toplevel
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Toplevel parser
--
--------------------------------------------------------------------------------

module Language.ILC.Parser.Toplevel (
      parser
    ) where

import Text.Parsec
import Text.Parsec.String (Parser)

import Language.ILC.Decl
import Language.ILC.Lexer
import Language.ILC.Parser.Decl

contents :: Parser a -> Parser a
contents p = mklexer id $ whitespace *> p <* eof

toplevel :: Parser [TopDecl]
toplevel = many1 decl

parser :: String -> Either ParseError [TopDecl]
parser = parse (contents toplevel) "<stdin>"
