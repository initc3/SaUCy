{-# OPTIONS_GHC -Wall #-}
------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Parser.Expr
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Expression parser
--
--------------------------------------------------------------------------------

module Language.ILC.Parser.Expr (
    expr
) where

import Data.Functor.Identity (Identity)
import Text.Parsec
import qualified Text.Parsec.Expr as Ex
import Text.Parsec.String (Parser)

import Language.ILC.Lexer
import Language.ILC.Parser.Pattern
import Language.ILC.Syntax

-- | Parse expressions

eVar :: Parser Expr
eVar = mklexer EVar identifier

eCon :: Parser Expr
eCon = mklexer EVar constructor

-- | Literals

eInt :: Parser Expr
eInt = mklexer (ELit . LInt) integer

eBool :: Parser Expr
eBool = eTrue <|> eFalse
  where
    eTrue  = reserved "true"  >> return (ELit $ LBool True)
    eFalse = reserved "false" >> return (ELit $ LBool False)

eString :: Parser Expr
eString = mklexer (ELit . LString) stringLit  

eUnit :: Parser Expr
eUnit = reserved "()" >> return (ELit LUnit)

eTuple :: Parser Expr
eTuple = mklexer ETuple $ parens $ commaSep2 expr

eList :: Parser Expr
eList = mklexer EList $ brackets $ commaSep expr

eLam :: Parser Expr
eLam = do
  reserved "lam"
  x <- pat
  reserved "."
  ELam x <$> expr

eLam1 :: Parser Expr
eLam1 = do
  reserved "lam1"
  x <- pat
  reserved "."
  ELam1 x <$> expr

eLamw :: Parser Expr
eLamw = do
  reserved "lamw"
  x <- pat
  reserved "."
  ELamw x <$> expr    

eApp :: Expr -> Parser Expr
eApp f = do
  args <- many1 atomExpr
  return $ foldl EApp f args

atoms :: Parser Expr
atoms = atomExpr >>= \a ->
        eApp a <|> return a

eFix :: Parser Expr
eFix = do
  reserved "fix"
  x <- identifier
  reserved "."
  EFix x <$> expr

eLets :: Parser Expr
eLets = reserved "let" *> (try normalLet <|> eLetRd)

normalLet :: Parser Expr
normalLet = do
  ps <- commaSep1 pat
  reservedOp "="
  e1 <- expr
  reserved "in"
  e2 <- expr
  return $ foldr (`ELet` e1) e2 ps

eLetRd :: Parser Expr
eLetRd = do
  p <- pat
  reservedOp "="
  reservedOp "rd"
  e1 <- expr
  reserved "in"
  ELetRd p (ERd e1) <$> expr

eIf :: Parser Expr
eIf = do
  reserved "if"
  b <- expr
  reserved "then"
  e <- expr
  reserved "else"
  EIf b e <$> expr

branch :: Parser (Pattern, Expr, Expr)
branch = do
  reservedOp "|"
  p <- pat
  g <- option (ELit $ LBool True) guard
  reservedOp "=>"
  e <- expr
  return (p, g, e)

guard :: Parser Expr
guard = do
  reserved "when"
  expr

eMatch :: Parser Expr      
eMatch = do
  reserved "match"
  e <- expr
  reserved "with"
  bs <- many1 branch
  return $ EMatch e bs

chan1 :: Parser (Name, Name)
chan1 = do
  c <- identifier
  return (c, c ++ "'")

chanPair :: Parser (Name, Name)
chanPair = do
  c1 <- identifier
  _  <- comma
  c2 <- identifier
  return (c1, c2)

chan2 :: Parser (Name, Name)
chan2 = parens chanPair

chan :: Parser (Name, Name)
chan = chan1 <|> chan2

eNu :: Parser Expr
eNu = do
  reserved "nu"
  cs <- commaSep1 chan
  reserved "."
  e <- expr
  return $ foldr ENu e cs

eWr :: Parser Expr
eWr = do
  reserved "wr"
  e <- expr
  reserved "->"
  EWr e <$> atomExpr

eFork :: Expr -> Parser Expr
eFork e = do
  reservedOp "|>"
  EFork e <$> expr

eChoice :: Expr -> Parser Expr    
eChoice e = do
  reservedOp "<|>"
  EChoice e <$> expr

eSeq :: Expr -> Parser Expr
eSeq e = do
  reserved ";"
  ELet PWildcard e <$> expr
  
table :: [[Ex.Operator String () Identity Expr]]
table = [ [ binaryOp "*" (EBin Mul) Ex.AssocLeft
          , binaryOp "/" (EBin Div) Ex.AssocLeft ]
        , [ binaryOp "%" (EBin Mod) Ex.AssocLeft ]
        , [ binaryOp "+" (EBin Add) Ex.AssocLeft
          , binaryOp "-" (EBin Sub) Ex.AssocLeft ]
        , [ prefixOp "~" (EUn Not) ]
        , [ binaryOp ":" (EBin Cons) Ex.AssocRight
          , binaryOp "++" (EBin Concat) Ex.AssocLeft ]
        , [ binaryOp "<" (EBin Lt) Ex.AssocNone
          , binaryOp ">" (EBin Gt) Ex.AssocNone
          , binaryOp "<=" (EBin Leq) Ex.AssocNone
          , binaryOp ">=" (EBin Geq) Ex.AssocNone
          , binaryOp "==" (EBin Eql) Ex.AssocNone
          , binaryOp "<>" (EBin Neq) Ex.AssocNone
          ]
        , [ binaryOp "&&" (EBin And) Ex.AssocLeft ]
        , [ binaryOp "||" (EBin Or) Ex.AssocLeft ]
        ]

ePrint :: Parser Expr
ePrint = mklexer EPrint $ reserved "print" >> atomExpr

eError :: Parser Expr
eError = mklexer EError $ reserved "error" >> atomExpr

eBang :: Parser Expr
eBang = mklexer EBang $ reservedOp "!" >> atomExpr

eUn :: Parser Expr
eUn = ePrint <|> eError

atomExpr :: Parser Expr
atomExpr = eVar
  <|> eCon
  <|> eInt
  <|> eBool
  <|> eString
  <|> eList
  <|> eBang
  <|> try eUnit
  <|> try eTuple
  <|> parens expr

term :: Parser Expr
term = atoms
  <|> eLam  
  <|> eLam1
  <|> eLamw
  <|> eFix    
  <|> eLets
  <|> eIf
  <|> eMatch
  <|> eNu
  <|> eWr
  <|> eUn

expr' :: Parser Expr
expr' = Ex.buildExpressionParser table term

expr :: Parser Expr
expr = expr' >>= \e ->
       eFork e <|> eChoice e <|> eSeq e <|> return e
