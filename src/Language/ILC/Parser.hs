{-# LANGUAGE TemplateHaskell #-}
------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Parser
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Parse source into an AST.
--
--------------------------------------------------------------------------------

module Language.ILC.Parser (
      parser
    ) where

import Data.Functor.Identity (Identity)
import Development.Placeholders
import Text.Parsec
import qualified Text.Parsec.Expr as Ex
import Text.Parsec.String (Parser)

import Language.ILC.Decl
import Language.ILC.Lexer
import Language.ILC.Type
import Language.ILC.Syntax

-- | Parse expressions

eVar :: Parser Expr
eVar = mklexer EVar identifier

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

eSett :: Parser Expr
eSett = mklexer ESett $ braces $ commaSep expr

eLam :: Parser Expr
eLam = do
    reserved "lam"
    x <- pat
    reserved "."
    ELam x <$> expr

eApp :: Parser Expr
eApp = do
    f <- atomExpr
    args <- many1 atomExpr
    return $ foldl EApp f args

eFix :: Parser Expr
eFix = $(todo "Parse fixed point expressions")

normalLet :: Parser Expr
normalLet = do
    reserved "let"
    ps <- commaSep1 pat
    reservedOp "="
    e1 <- expr
    reserved "in"
    e2 <- expr
    return $ foldr (`ELet` e1) e2 ps

recursiveLet :: Parser Expr
recursiveLet = do
    reserved "letrec"
    p <- pat
    args <- many1 pat
    reservedOp "="
    e <- expr
    reserved "in"
    ELet p (EFix $ foldr ELam e (p:args)) <$> expr

eLet :: Parser Expr
eLet = try recursiveLet <|> normalLet

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
chan2 = do
    cs <- parens chanPair
    return cs

chan :: Parser (Name, Name)
chan = try chan1 <|> chan2

eNu :: Parser Expr
eNu = do
    reserved "nu"
    cs <- commaSep1 chan
    reserved "."
    e <- expr
    return $ foldr ENu e cs

eRd :: Parser Expr
eRd = mklexer ERd $ reserved "rd" >> atomExpr

eWr :: Parser Expr
eWr = do
    reserved "wr"
    e <- expr
    reserved "->"
    EWr e <$> atomExpr

eFork :: Parser Expr
eFork = do
    e <- expr'
    reservedOp "|>"
    EFork e <$> expr

eChoice :: Parser Expr    
eChoice = do
    e <- expr'
    reservedOp "<|>"
    EChoice e <$> expr

eRef :: Parser Expr
eRef = mklexer ERef $ reserved "ref" >> atomExpr

eGet :: Parser Expr
eGet = mklexer EGet $ reservedOp "@" >> atomExpr

eSet :: Parser Expr
eSet = do
    reserved "let"
    x <- identifier
    reservedOp ":="
    ESet x <$> expr

eSeq :: Parser Expr
eSeq = do
    e <- expr'
    reserved ";"
    ESeq e <$> expr
  
table :: [[Ex.Operator String () Identity Expr]]
table = [ [ binaryOp "*" (EBin Mul) Ex.AssocLeft
          , binaryOp "/" (EBin Div) Ex.AssocLeft ]
        , [ binaryOp "%" (EBin Mod) Ex.AssocLeft ]
        , [ binaryOp "+" (EBin Add) Ex.AssocLeft
          , binaryOp "-" (EBin Sub) Ex.AssocLeft ]
        , [ prefixOp "!" (EUn Not) ]
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

eThunk :: Parser Expr
eThunk = mklexer EThunk $ reserved "thunk" >> atomExpr

eForce :: Parser Expr
eForce = mklexer EForce $ reserved "force" >> atomExpr

ePrint :: Parser Expr
ePrint = mklexer EPrint $ reserved "print" >> atomExpr

eError :: Parser Expr
eError = mklexer EError $ reserved "error" >> atomExpr

eUn :: Parser Expr
eUn = eThunk
   <|> eForce
   <|> ePrint
   <|> eError


eCustom :: Parser Expr
eCustom = do
  con <- constructor
  exprs <- many atomExpr
  return $ ECustom con exprs

expr :: Parser Expr
expr = try eSeq <|> try eChoice <|> try eFork <|> expr'

expr' :: Parser Expr
expr' = Ex.buildExpressionParser table term

atomExpr :: Parser Expr
atomExpr = eVar
       <|> eInt
       <|> eBool
       <|> eString
       <|> eList
       <|> eSett
       <|> try eUnit
       <|> try eTuple
       <|> parens expr

term :: Parser Expr
term = try eApp
   <|> atomExpr
   <|> eLam
   <|> try eSet
   <|> eLet
   <|> eIf
   <|> eMatch
   <|> eNu
   <|> eRd
   <|> eWr
   <|> eRef
   <|> eGet
   <|> eUn
   <|> eCustom

-- | Patterns

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
    PCons hd <$> pat'

pSet :: Parser Pattern
pSet = mklexer PSet $ braces $ commaSep pat

-- TODO: Fix parens parsing
pCust :: Parser Pattern
pCust = do
  optional $ whitespace *> char '('
  con <- constructor
  ps <- many pat
  optional $ char ')' <* whitespace
  return $ PCust con ps
  
-- TODO: Use chainl1?
pat :: Parser Pattern
pat = try pCons <|> pat'

pat' :: Parser Pattern
pat' = pVar
  <|> pInt
  <|> pBool
  <|> pString
  <|> try pUnit
  <|> pWildcard
  <|> try pTuple
  <|> pList
  <|> pSet
  <|> pCust

-- | Parse toplevel declarations

dExpr :: Parser TopDecl
dExpr = do
  e <- expr
  optional $ reserved ";;"
  return $ Decl "it" e

parseLet :: Parser (Name, [Pattern], Expr)
parseLet = do
  x <- identifier
  ps <- many pat
  reserved "="
  e <- expr
  optional $ reserved ";;"
  return (x, ps, e)

dDeclLetRec :: Parser TopDecl
dDeclLetRec = do
  reserved "letrec"
  (x, ps, e) <- parseLet
  return $ Decl x (EFix $ foldr ELam e (PVar x : ps))

dDeclFun :: Parser TopDecl
dDeclFun = do
  reserved "let"
  (x, ps, e) <- parseLet
  return $ Decl x (foldr ELam e ps)

dDeclCon :: Parser TopDecl
dDeclCon = do
  reserved "data"
  tyCon <- constructor
  reservedOp "="
  valCons <- sepBy1 parseValCon (reservedOp "|")
  return $ TyCon tyCon valCons
  
parseValCon :: Parser ValCon
parseValCon = do
  valCon <- constructor
  params <- sepBy parseTy whitespace
  return (valCon, params)

decl :: Parser TopDecl
decl = dDeclCon <|> try dExpr <|> try dDeclLetRec <|> dDeclFun

-- | Parse types

parseTyInt, parseTyBool, parseTyString :: Parser Type  
parseTyInt = mklexer (const tyInt) $ reserved "Int"
parseTyBool = mklexer (const tyBool) $ reserved "Bool"
parseTyString = mklexer (const tyString) $ reserved "String"

parseTy :: Parser Type
parseTy = parseTyInt <|> parseTyBool <|> parseTyString

-- | Toplevel parser

contents :: Parser a -> Parser a
contents p = mklexer id $ whitespace *> p <* eof

toplevel :: Parser [TopDecl]
toplevel = many1 decl

parser :: String -> Either ParseError [TopDecl]
parser = parse (contents toplevel) "<stdin>"
