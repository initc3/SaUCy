{-# OPTIONS_GHC -Wall #-}
------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Parser.Decl
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Declaration parser
--
--------------------------------------------------------------------------------

module Language.ILC.Parser.Decl (
    decl
) where

import Text.Parsec
import Text.Parsec.String (Parser)

import Language.ILC.Decl
import Language.ILC.Lexer
import Language.ILC.Parser.Expr
import Language.ILC.Parser.Pattern
import Language.ILC.Parser.Type
import Language.ILC.Syntax
import Language.ILC.Type

-- | Parse toplevel declarations

dExpr :: Parser TopDecl
dExpr = Decl "it" <$> expr

parseLet :: Parser (Name, [Pattern], Expr)
parseLet = do
  x <- identifier
  ps <- many pat
  reserved "="
  e <- expr
  return (x, ps, e)

dDeclLetRec :: Parser TopDecl
dDeclLetRec = do
  reserved "letrec"
  (x, ps, e) <- parseLet
  return $ Decl x (EFix x $ foldr ELam e ps)  

dDeclFun :: Parser TopDecl
dDeclFun = do
  reserved "let"
  (x, ps, e) <- parseLet
  return $ Decl x (foldr ELam e ps)

dDeclCon :: Parser TopDecl
dDeclCon = do
  reserved "data"
  tyCon <- constructor
  _ <- many identifier
  reservedOp "="
  valCons <- sepBy1 (parseValCon tyCon) (reservedOp "|")
  return $ TyCon tyCon valCons
  
parseValCon :: Name -> Parser ValCon
parseValCon tyCon = do
  valCon <- constructor
  params <- sepBy ty whitespace
  let ps = map stripi params
  return (valCon, foldr (\a b -> IType (IArr a b)) (IType (ISend (SCon tyCon))) ps)

decl :: Parser TopDecl
decl = dDeclCon <|> dDeclLetRec <|> try dExpr <|> dDeclFun
