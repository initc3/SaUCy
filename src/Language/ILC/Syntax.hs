--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Syntax
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Defines the ILC abstract syntax tree (expressions), values, the term
-- environment, and environment functions.
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
  , Value(..)
  , TermEnv
  , emptyTmEnv
  , extendTmEnv
  ) where

import Control.Concurrent
import Data.IORef
import qualified Data.Map.Strict as Map
import Text.PrettyPrint.ANSI.Leijen

import Language.ILC.Pretty

-- | Variable names
type Name = String

-- | Expressions
data Expr = EVar Name
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
data Lit = LInt Integer
         | LBool Bool
         | LString String
         | LTag String
         | LUnit
         deriving (Eq, Show)

-- | Binary operators
data Binop = Add
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
data Unop = Not deriving (Eq, Show)

-- | Patterns
data Pattern = PVar Name
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

instance Pretty Pattern where
  pretty (PVar x) = text x
  pretty (PInt n) = integer n
  pretty (PBool True) = text "true"
  pretty (PBool False) = text "false"
  pretty (PString s)   = text s
  pretty (PTag t)      = text t
  pretty PUnit         = text "()"
  pretty PWildcard     = text "_"
  pretty (PTuple ps)   = prettyTuple $ map pretty ps
  pretty (PList ps)    = prettyList ps
  pretty (PCons hd tl) = pretty hd <+> text ":" <+> pretty tl
  pretty (PSet ps)     = prettySet $ map pretty ps

-- | Toplevel declarations
type Decl = (Name, Expr)

-- | Program with main expression
data Program = Program [Decl] Expr  -- TODO: Main
  deriving (Eq, Show)

-- | Values
data Value = VInt Integer
           | VBool Bool
           | VString String
           | VTag String
           | VList [Value]
           | VSet [Value]
           | VTuple [Value]
           | VUnit
           | VClosure (Maybe Name) TermEnv Expr
           | VThunk TermEnv Expr
           | VRdChan Name (Chan Value)
           | VWrChan Name (Chan Value)
           | VRef (IORef Value)
           deriving (Show, Eq)

instance Show (IORef a) where
  show _ = "IORef"

instance Show (Chan a) where
  show _ = "Chan"

instance Pretty Value where
  pretty (VInt n)      = integer n
  pretty (VBool True)  = text "true"
  pretty (VBool False) = text "false"
  pretty (VString s)   = text s
  pretty (VTag t)      = text t
  pretty (VList vs)    = prettyList vs
  pretty (VTuple vs)   = prettyTuple $ map pretty vs
  pretty (VSet vs)     = prettySet $ map pretty vs
  pretty VUnit         = text "()"
  pretty VClosure{}    = text "<closure>"
  pretty VThunk{}      = text "<thunk>"
  pretty (VRdChan c _) = text "Rd" <+> text c
  pretty (VWrChan c _) = text "Wr" <+> text c
  pretty (VRef _)      = text "<ref>"
  
-- | Term environment is a map from names to values
type TermEnv = Map.Map Name Value

-- | Empty term environment
emptyTmEnv :: TermEnv
emptyTmEnv = Map.empty

-- | Extend term environment
extendTmEnv :: TermEnv -> Name -> Value -> TermEnv
extendTmEnv env x v = Map.insert x v env
