------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Parser.Type
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Type parser
--
--------------------------------------------------------------------------------

module Language.ILC.Parser.Type (
    ty
) where

import Text.Parsec
import Text.Parsec.String (Parser)

import Language.ILC.Lexer
import Language.ILC.Type

tPrim :: Parser Type
tPrim = tInt <|> tBool <|> tString <|> tUnit
  where
    tInt    = reserved "Int"    >> return (IType tyInt)
    tBool   = reserved "Bool"   >> return (IType tyBool)
    tString = reserved "String" >> return (IType tyString)
    tUnit   = reserved "Unit"   >> return (IType tyUnit)    

tVar, tCon, tList, tProd, tRd, tWr :: Parser Type
tVar  = mklexer (IType . IVar . TV) identifier
tCon  = mklexer (IType . ICon) constructor
tList = mklexer (IType . IList) $ brackets $ stripi <$> ty
tProd = mklexer (IType . IProd) $ parens $ commaSep2 $ stripi <$> ty
tRd   = mklexer (AType . ARdChan) $ reserved "Rd" >> strips <$> ty'
tWr   = mklexer (IType . IWrChan) $ reserved "Wr" >> strips <$> ty'

tArrow :: Parser Type
tArrow = do
  IType t1 <- ty'
  reserved "->"
  IType . IArr t1 <$> ty

ty' :: Parser Type
ty' = tPrim
  <|> tVar
  <|> tCon
  <|> tList
  <|> try tProd
  <|> tRd
  <|> tWr
  <|> parens tArrow

ty :: Parser Type  
ty = try tArrow <|> ty'  
