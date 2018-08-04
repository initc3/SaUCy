module Parser
    (
      parser
    ) where

import Data.Functor.Identity (Identity)
import Text.Parsec
import qualified Text.Parsec.Expr as Ex
import Text.Parsec.String (Parser)

import Lexer
import Syntax

{-tInt = reserved "Int" >> return TInt

tBool = reserved "Bool" >> return TBool

tString = reserved "String" >> return TString

tChan = reserved "Chan" >> return TChan

tProd = mklexer TProd $ parens $ commaSep2 ty

tRd = mklexer TRd $ reserved "Rd" >> ty

tWr = mklexer TWr $ reserved "Wr" >> ty

tArrow = do
    t1 <- ty'
    reserved "->"
    t2 <- ty
    TArrow t1 <$> t2

tList = mklexer TList $ brackets $ ty    

ty = try tArrow <|> ty'
ty' = tInt
  <|> tBool
  <|> tString
  <|> tChan
  <|> tProd
  <|> tList
  <|> tRd
  <|> tWr-}

-- | Parse expressions

eVar = mklexer EVar identifier

eImpVar = mklexer EImpVar $ char '?' >> identifier

-- | Literals

eInt = mklexer (ELit . LInt) integer

eBool = eTrue <|> eFalse
  where
    eTrue  = reserved "true"  >> return (ELit $ LBool True)
    eFalse = reserved "false" >> return (ELit $ LBool False)

eString = mklexer (ELit . LString) stringLit  

eTag = mklexer (ELit . LTag) $ char '\'' >> identifier

eUnit = reserved "()" >> return (ELit LUnit)

eTuple = mklexer ETuple $ parens $ commaSep2 expr

eList = mklexer EList $ brackets $ commaSep expr

eSet = mklexer ESet $ braces $ commaSep expr

eLam = do
    reserved "lam"
    x <- pat
    reserved "."
    ELam x <$> expr

eApp = do
    f <- atomExpr
    args <- many1 atomExpr
    return $ foldl EApp f args

-- TODO: EFix

normalLet = do
    reserved "let"
    ps <- commaSep1 pat
    reservedOp "="
    e1 <- expr
    reserved "in"
    e2 <- expr
    return $ foldr (`ELet` e1) e2 ps

recursiveLet = do
    reserved "letrec"
    p <- pat
    args <- many1 pat
    reservedOp "="
    e <- expr
    reserved "in"
    ELet p (EFix $ foldr ELam e (p:args)) <$> expr
    
eLet = try recursiveLet <|> normalLet

eIf = do
    reserved "if"
    b <- expr
    reserved "then"
    e <- expr
    reserved "else"
    EIf b e <$> expr

branch = do
    reservedOp "|"
    p <- pat
    g <- option (ELit $ LBool True) guard
    reservedOp "=>"
    e <- expr
    return (p, g, e)

guard = do
    reserved "when"
    expr
      
eMatch = do
    reserved "match"
    e <- expr
    reserved "with"
    bs <- many1 branch
    return $ EMatch e bs

eNu = do
    reserved "nu"
    c <- identifier
    reserved "."
    ENu c <$> expr

eRd = mklexer ERd $ reserved "rd" >> atomExpr

eWr = do
    reserved "wr"
    e <- expr
    reserved "->"
    EWr e <$> atomExpr

eFork = do
    e1 <- expr'
    reservedOp "|>"
    EFork e1 <$> expr

eRepl = mklexer ERepl $ reservedOp "!" >> atomExpr  

eRef = mklexer ERef $ reserved "ref" >> atomExpr

eDeref = mklexer EDeref $ reservedOp "@" >> atomExpr

eAssign = do
    reserved "let"
    x <- identifier
    reservedOp ":="
    EAssign x <$> expr

eSeq = do
    e <- expr'
    reserved ";"
    ESeq e <$> expr
  
table :: [[Ex.Operator String () Identity Expr]]
table = [ [ binaryOp "*" (EBinArith Mul) Ex.AssocLeft
          , binaryOp "/" (EBinArith Div) Ex.AssocLeft ]
        , [ binaryOp "%" (EBinArith Mod) Ex.AssocLeft ]
        , [ binaryOp "+" (EBinArith Add) Ex.AssocLeft
          , binaryOp "-" (EBinArith Sub) Ex.AssocLeft ]
        , [ prefixOp "not" (EUnBool Not) ]
        , [ binaryOp ":" (EBin Cons) Ex.AssocRight
          , binaryOp "++" (EBin Concat) Ex.AssocLeft ]
        , [ binaryOp "<" (EBinRel Lt) Ex.AssocNone
          , binaryOp ">" (EBinRel Gt) Ex.AssocNone
          , binaryOp "<=" (EBinRel Leq) Ex.AssocNone
          , binaryOp ">=" (EBinRel Geq) Ex.AssocNone
          , binaryOp "==" (EBinRel Eql) Ex.AssocNone
          , binaryOp "<>" (EBinRel Neq) Ex.AssocNone
          ]
        , [ binaryOp "&&" (EBinBool And) Ex.AssocLeft ]
        , [ binaryOp "||" (EBinBool Or) Ex.AssocLeft ]
        ]

eThunk = mklexer (EUn Thunk) $ reserved "thunk" >> atomExpr

eForce = mklexer (EUn Force) $ reserved "force" >> atomExpr

ePrint = mklexer (EUn Print) $ reserved "print" >> atomExpr

eError = mklexer (EUn Syntax.Error) $ reserved "error" >> atomExpr

eUn = eThunk
   <|> eForce
   <|> ePrint
   <|> eError

expr = try eSeq <|> try eFork <|> expr'

expr' = Ex.buildExpressionParser table term

atomExpr = eVar
       <|> eImpVar
       <|> eInt
       <|> eBool
       <|> eString
       <|> eTag
       <|> eList
       <|> eSet
       <|> try eUnit
       <|> try eTuple
       <|> parens expr

term = try eApp
   <|> atomExpr
   <|> eLam
   <|> try eAssign
   <|> eLet
   <|> eIf
   <|> eMatch
   <|> eNu
   <|> eRd
   <|> eWr
   <|> eRepl
   <|> eRef
   <|> eDeref
   <|> eUn

-- | Patterns

pVar = mklexer PVar identifier

pInt = mklexer PInt integer

pBool = pTrue <|> pFalse
  where
    pTrue = reserved "true" >> return (PBool True)
    pFalse = reserved "false" >> return (PBool False)

pString = mklexer PString stringLit

pTag = mklexer PTag $ char '\'' >> identifier

pUnit = reserved "()" >> return PUnit

pWildcard = reserved "_" >> return PWildcard

pTuple = mklexer PTuple $ parens $ commaSep2 pat
  
pList = mklexer PList $ brackets $ commaSep pat

pCons = do
    hd <- pat'
    colon
    PCons hd <$> pat'

pSet = mklexer PSet $ braces $ commaSep pat

-- TODO: Use chainl1?
pat = try pCons <|> pat'

pat' = pVar
  <|> pInt
  <|> pBool
  <|> pString
  <|> pTag
  <|> try pUnit
  <|> pWildcard
  <|> pTuple
  <|> pList
  <|> pSet

-- | Parse toplevel declarations

dExpr = do
    e <- expr
    optional $ reserved ";;"
    return ("it", e)

parseLet = do
    x <- identifier
    ps <- many pat
    reserved "="
    e <- expr
    optional $ reserved ";;"
    return (x, ps, e)

dDeclLetRec = do
    reserved "letrec"
    (x, ps, e) <- parseLet
    return (x, EFix $ foldr ELam e (PVar x : ps))

dDeclFun = do
    reserved "let"
    (x, ps, e) <- parseLet
    return (x, foldr ELam e ps)

{-tySig = do
  x <- identifier
  reserved "::"
  t <- ty
  return $ TySig x t-}

decl = try dExpr <|> try dDeclLetRec <|> dDeclFun

-- | Toplevel parser

contents :: Parser a -> Parser a
contents p = mklexer id $ whitespace *> p <* eof

toplevel :: Parser [Decl]
toplevel = many1 decl

parser :: String -> Either ParseError [Decl]
parser = parse (contents toplevel) "<stdin>"
