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

eApp :: Expr -> Parser Expr
eApp f = do
  -- f <- atomExpr
  args <- many1 atomExpr
  return $ foldl EApp f args

atoms = atomExpr >>= \a ->
        eApp a <|> return a

eFix :: Parser Expr
eFix = $(todo "Parse fixed point expressions")

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
  e2 <- expr
  return $ ELetRd p (ERd e1) e2

{-eLetRec :: Parser Expr
eLetRec = do
  reserved "letrec"
  p <- pat
  args <- many1 pat
  reservedOp "="
  e <- expr
  reserved "in"
  ELet p (EFix $ foldr ELam e (p:args)) <$> expr-}

eLetBang :: Parser Expr
eLetBang = do
  reserved "let!"
  ps <- commaSep1 pat
  reservedOp "="
  e1 <- expr
  reserved "in"
  e2 <- expr
  return $ foldr (`ELetBang` e1) e2 ps

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
eUn = ePrint
  <|> eError

expr :: Parser Expr
expr = expr' >>= \e ->
       eFork e <|> eChoice e <|> return e

expr' :: Parser Expr
expr' = Ex.buildExpressionParser table term

atomExpr :: Parser Expr
atomExpr =
      eVar
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
  <|> eLetBang
  <|> eLets
  <|> eIf
  <|> eMatch
  <|> eNu
  <|> eWr
  <|> eUn

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
  PCons hd <$> pat

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
pat' =
      pVar
  <|> pInt
  <|> pBool
  <|> pString
  <|> try pUnit
  <|> pWildcard
  <|> try pTuple
  <|> pList
  <|> pCust

-- | Parse toplevel declarations

dExpr :: Parser TopDecl
dExpr = do
  e <- expr
  return $ Decl "it" e

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
  _ <- many identifier
  reservedOp "="
  valCons <- sepBy1 (parseValCon tyCon) (reservedOp "|")
  return $ TyCon tyCon valCons
  
parseValCon :: Name -> Parser ValCon
parseValCon tyCon = do
  valCon <- constructor
  params <- sepBy ty whitespace
  let ps = params ++ [TCon valCon]
  return $ (valCon, foldr (\a b -> TArr a b) (TCon tyCon) params)

decl :: Parser TopDecl
decl = dDeclCon <|> dDeclLetRec <|> try dExpr <|> dDeclFun

-- | Parse types
tInt, tBool, tString, tUnit :: Parser Type  
tInt = mklexer (const tyInt) $ reserved "Int"
tBool = mklexer (const tyBool) $ reserved "Bool"
tString = mklexer (const tyString) $ reserved "String"
tUnit = mklexer (const tyUnit) $ reserved "Unit"

tPrim :: Parser Type
tPrim = tInt <|> tBool <|> tString <|> tUnit

tVar = mklexer (TVar . TV) identifier
tCon = mklexer TCon constructor
tList = mklexer TList $ brackets $ ty
tProd = mklexer TProd $ parens $ commaSep2 ty
tRd = mklexer TRdChan $ reserved "Rd" >> ty'
tWr = mklexer TWrChan $ reserved "Wr" >> ty'

tArrow = do
  t1 <- ty'
  reserved "->"
  t2 <- ty
  return $ TArr t1 t2
  
ty = try tArrow <|> ty'

ty' = tPrim
  <|> tVar
  <|> tCon
  <|> tList
  <|> try tProd
  <|> tRd
  <|> tWr
  <|> parens tArrow

-- | Toplevel parser

contents :: Parser a -> Parser a
contents p = mklexer id $ whitespace *> p <* eof

toplevel :: Parser [TopDecl]
toplevel = many1 decl

parser :: String -> Either ParseError [TopDecl]
parser = parse (contents toplevel) "<stdin>"
