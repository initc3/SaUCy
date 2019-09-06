--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Lexer
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Lexing functions
--
--------------------------------------------------------------------------------

module Language.ILC.Lexer (
    whitespace
  , identifier
  , constructor
  , integer
  , stringLit
  , parens
  , brackets
  , braces
  , reserved
  , colon
  , comma
  , commaSep
  , commaSep1
  , commaSep2
  , reservedOp
  , binaryOp
  , prefixOp
  , mklexer
) where

import Data.Functor.Identity (Identity)
import Data.Semigroup ((<>))
import Text.Parsec
import Text.Parsec.String (Parser)

import Language.ILC.Syntax

import qualified Text.Parsec.Expr as Ex
import qualified Text.Parsec.Token as Tok

langDef :: Tok.LanguageDef ()
langDef = Tok.LanguageDef
    { Tok.commentStart = "{-"
    , Tok.commentEnd   = "-}"
    , Tok.commentLine  = "--"
    , Tok.nestedComments = True
    , Tok.identStart = lower
    , Tok.identLetter = alphaNum <|> oneOf "_'"
    , Tok.opStart = oneOf ":!#$%&*+.?<=>?@\\^|-~"
    , Tok.opLetter = oneOf ":!#$%&*+.?<=>?@\\^|-~"
    , Tok.reservedNames = [ "let"
                          , "in"
                          , "letrec"
                          , "lam"
                          , "lamw"                          
                          , "lam1"
                          , "fix"                          
                          , "rd"
                          , "wr"
                          , "nu"
                          , "not"
                          , "if"
                          , "then"
                          , "else"
                          , "true"
                          , "false"
                          , "match"
                          , "with"
                          , "when"
                          , "print"
                          , "error"
                          , "data"                          
                          , "Int"
                          , "Bool"
                          , "String"
                          , "Chan"
                          , "Rd"
                          , "Wr"
                          ]
    , Tok.reservedOpNames = [ "+"
                            , "-"
                            , "*"
                            , "/"
                            , "%"
                            , "&&"
                            , "||"
                            , "<"
                            , ">"
                            , "<="
                            , ">="
                            , "=="
                            , "<>"
                            , "~"
                            , "|>"
                            , ";"
                            , ":"
                            , "++"
                            , "::"
                            , ":="
                            , "!"
                            ]
    , Tok.caseSensitive = True
    }

lexer :: Tok.TokenParser ()
lexer = Tok.makeTokenParser langDef

whitespace :: Parser ()
whitespace = Tok.whiteSpace lexer

identifier :: Parser Name
identifier = Tok.identifier lexer

constructor :: Parser Name
constructor = many1 upper <> many (alphaNum <|> oneOf "_'") <* whitespace

-- TODO: Parse negative integers
integer :: Parser Integer
integer = Tok.natural lexer

stringLit :: Parser String
stringLit = Tok.stringLiteral lexer

parens :: Parser a -> Parser a
parens = Tok.parens lexer

brackets :: Parser a -> Parser a
brackets = Tok.brackets lexer

braces :: Parser a -> Parser a
braces = Tok.braces lexer

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

colon :: Parser String
colon = Tok.colon lexer

semi :: Parser String
semi = Tok.semi lexer

semiSep :: Parser a -> Parser [a]
semiSep = Tok.semiSep lexer

comma :: Parser String
comma = Tok.comma lexer

commaSep :: Parser a -> Parser [a]
commaSep = Tok.commaSep lexer

commaSep1 :: Parser a -> Parser [a]
commaSep1 = Tok.commaSep1 lexer

(<:>) :: (Applicative f) => f a -> f [a] -> f [a]
(<:>) a b = (:) <$> a <*> b

commaSep2 :: Parser a -> Parser [a]
commaSep2 p = (p <* comma) <:> commaSep1 p

reservedOp :: String -> Parser ()
reservedOp = Tok.reservedOp lexer

prefixOp :: String -> (a -> a) -> Ex.Operator String () Identity a
prefixOp s f = Ex.Prefix (reservedOp s >> return f)

binaryOp :: String -> (a -> a -> a) -> Ex.Assoc -> Ex.Operator String () Identity a
binaryOp s f = Ex.Infix (reservedOp s >> return f)

mklexer :: (a -> b) -> Parser a -> Parser b
mklexer e p = p >>= \x -> return (e x)
