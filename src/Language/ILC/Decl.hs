--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Decl
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Defines top level declarations.
--
--------------------------------------------------------------------------------

module Language.ILC.Decl (
    TopDecl(..)
  , ValCon
  , declToAssoc
  ) where

import Language.ILC.Pretty
import Language.ILC.Syntax
import Language.ILC.Type

-- | A toplevel declaration binds an expression to a variable name.
data TopDecl = Decl Name Expr
             | TyCon Name [ValCon]
             deriving (Eq, Show)

type ValCon = (Name, [Type])

-- | A program consists of a list of declarations and a main expression.
data Program = Program [TopDecl] Expr
             deriving (Eq, Show)

declToAssoc :: [TopDecl] -> [(Name, Expr)]
declToAssoc ds = foldl f [] ds
  where f acc (Decl x e) = (x, e) : acc
        f acc _          = acc
