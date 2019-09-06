{-# OPTIONS_GHC -Wall #-}
------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Parser.Pattern
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Pattern parser
--
--------------------------------------------------------------------------------

module Language.ILC.Parser.Pattern (
    pat
) where

import Text.Parsec
import Text.Parsec.String (Parser)

import Language.ILC.Lexer
import Language.ILC.Syntax

pVar :: Parser Pattern
pVar = mklexer PVar identifier

pInt :: Parser Pattern
pInt = mklexer PInt integer

pBool :: Parser Pattern
pBool = pTrue <|> pFalse
  where
    pTrue = reserved "true" >> return (PBool True)
    pFalse = reserved "false" >> return (PBool False)

pString :: Parser Pattern
pString = mklexer PString stringLit

pUnit :: Parser Pattern
pUnit = reserved "()" >> return PUnit

pWildcard :: Parser Pattern
pWildcard = reserved "_" >> return PWildcard

pTuple :: Parser Pattern
pTuple = mklexer PTuple $ parens $ commaSep2 pat
  
pList :: Parser Pattern
pList = mklexer PList $ brackets $ commaSep pat

pCons :: Parser Pattern
pCons = do
  hd <- pat'
  _  <- colon
  PCons hd <$> pat

pCust :: Parser Pattern
pCust = do
  con <- constructor
  ps <- many pat
  return $ PCust con ps

pGnab :: Parser Pattern
pGnab = do
  reservedOp "!"
  PGnab <$> pat
  
pat' :: Parser Pattern
pat' = pVar
  <|> pInt
  <|> pBool
  <|> pString
  <|> try pUnit
  <|> pWildcard
  <|> try pTuple
  <|> pList
  <|> pCust
  <|> pGnab
  <|> parens pat

pat :: Parser Pattern
pat = try pCons <|> pat'
