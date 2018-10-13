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
  , getCustomData
  , buildCustExpr
  , custTyToExpr
  ) where

import Language.ILC.Infer
import Language.ILC.Mode
import Language.ILC.Pretty
import Language.ILC.Syntax
import Language.ILC.Type

-- | A toplevel declaration binds an expression to a variable name.
data TopDecl = Decl Name Expr
             | TyCon Name [ValCon]
             deriving (Eq, Show)

type ValCon = (Name, Type)

-- | A program consists of a list of declarations and a main expression.
data Program = Program [TopDecl] Expr
             deriving (Eq, Show)

declToAssoc :: [TopDecl] -> [(Name, Expr)]
declToAssoc ds = reverse $ foldl f [] ds
  where f acc (Decl x e) = (x, e) : acc
        f acc _          = acc

getCustomData :: [TopDecl] -> [(Name, Scheme)]
getCustomData ds = reverse $ foldl f [] ds
  where f acc (TyCon dc vcs) = (map (\(vc,ty) -> (vc, closeOver ty)) vcs) ++ acc
        f acc _             = acc

buildCustExpr :: [TopDecl] -> [(Name, Expr)]
buildCustExpr ds = reverse $ foldl f [] ds
  where f acc (TyCon dc vcs) = map (\(x,t) -> (x, custTyToExpr (x,t) 1)) vcs ++ acc
        f acc _              = acc

custTyToExpr :: ValCon -> Int -> Expr
custTyToExpr (x,t) i = case t of
  TArr _ t'@(TArr{}) _ -> ELam (PVar (show i)) (custTyToExpr (x, t') (i + 1))
  TArr{}               -> ELam (PVar (show i)) (ECustom x (map (EVar . show) [1..i]))
  _                    -> ECustom x []
