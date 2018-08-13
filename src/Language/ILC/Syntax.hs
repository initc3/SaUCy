--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Syntax
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- ILC abstract syntax tree.
--
--------------------------------------------------------------------------------

module Language.ILC.Syntax (
      Name
    , Expr(..)
    , Lit(..)
    , Binop(..)
    , Unop(..)
    , Pattern(..)
    , Decl
    ) where

-- | Variable names
type Name = String

-- | Expressions
data Expr
    = EVar Name
    | EImpVar Name
    | ELit Lit
    | ETuple [Expr]
    | EList [Expr]
    | ESet [Expr]
    | ELam Pattern Expr
    | EApp Expr Expr
    | EFix Expr
    | ELet Pattern Expr Expr
    | EIf Expr Expr Expr
    | EMatch Expr [(Pattern, Expr, Expr)]
    | ENu (Name, Name) Expr
    | ERd Expr
    | EWr Expr Expr
    | EFork Expr Expr
    | EChoice Expr Expr
    | ERepl Expr
    | ERef Expr
    | EDeref Expr
    | EAssign Name Expr
    | ESeq Expr Expr
    | EThunk Expr
    | EForce Expr
    | EPrint Expr
    | EError Expr
    | EBin Binop Expr Expr
    | EUn Unop Expr
    deriving (Eq, Show)

-- | Literals
data Lit
    = LInt Integer
    | LBool Bool
    | LString String
    | LTag String
    | LUnit
    deriving (Eq, Show)

-- | Binary operators
data Binop
    = Add
    | Sub
    | Mul
    | Div
    | Mod
    | And
    | Or
    | Lt
    | Gt
    | Leq
    | Geq
    | Eql
    | Neq
    | Cons
    | Concat
    deriving (Eq, Show)

-- | Unary operator
data Unop
    = Not
    deriving (Eq, Show)

-- | Patterns
data Pattern
    = PVar Name
    | PInt Integer
    | PBool Bool
    | PString String
    | PTag String
    | PUnit
    | PWildcard
    | PTuple [Pattern]
    | PList [Pattern]
    | PCons Pattern Pattern
    | PSet [Pattern]
    deriving (Eq, Show)

-- | Toplevel declarations
type Decl = (Name, Expr)

-- | Program with main expression
data Program = Program [Decl] Expr  -- ^ TODO: Main
    deriving (Eq, Show)
