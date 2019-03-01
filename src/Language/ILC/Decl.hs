{-# OPTIONS_GHC -Wall #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Decl
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Defines top-level variable declarations and type declarations.
--
--------------------------------------------------------------------------------

module Language.ILC.Decl (
    TopDecl(..)
  , ValCon
  , declToAssoc
  , getCustomData
  , custTyToExpr
  ) where

import Language.ILC.Infer
import Language.ILC.Syntax
import Language.ILC.Type

-- | A top-level declaration either binds an expression to a name or defines a
-- new data type.
data TopDecl = Decl Name Expr
             | TyCon Name [ValCon]
             deriving (Eq, Show)

-- | A value or data constructor consists of a constructor name and its type.
type ValCon = (Name, Type)

-- | A program consists of a list of declarations and a main expression.
data Program = Program [TopDecl] Expr
             deriving (Eq, Show)

-- | Converts a variable declaration into an association list of names to
-- expressions.
declToAssoc :: [TopDecl] -> [(Name, Expr)]
declToAssoc ds = foldr f [] ds
  where f (Decl x e) acc = (x, e) : acc
        f _          acc = acc

-- | Converts a type declaration into an association list of names to type
-- schemes for custom data types.
getCustomData :: [TopDecl] -> [(Name, Scheme)]
getCustomData ds = foldr f [] ds
  where f (TyCon _ vcs) acc = map (\(vc,ty) -> (vc, closeOver ty)) vcs ++ acc
        f _             acc = acc
        
-- | Converts a value constructor into an expression for computing a custom data
-- type.
-- TODO: Generate fresh variables.
custTyToExpr :: ValCon -> Int -> Expr
custTyToExpr (x, TArr _ t@TArr{}) i =
  ELam (PVar (show i)) (custTyToExpr (x, t) (i + 1))
custTyToExpr (x, TArr{}) i =
  ELam (PVar (show i)) (ECustom x (map (EVar . show) [1..i]))
custTyToExpr (x,_) _ = ECustom x []
