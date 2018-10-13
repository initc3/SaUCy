{-# OPTIONS_GHC -Wall #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Syntax
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Defines the ILC abstract syntax tree.
--
--------------------------------------------------------------------------------

module Language.ILC.Syntax (
    Name
  , Expr(..)
  , Lit(..)
  , Binop(..)
  , Unop(..)
  , Pattern(..)
  ) where

import Text.PrettyPrint.ANSI.Leijen

import Language.ILC.Pretty

--------------------------------------------------------------------------------
-- ILC Syntax
--------------------------------------------------------------------------------

-- | Names in ILC.
type Name = String

-- | Expressions in ILC.
data Expr = EVar Name                            -- ^ Variable
          | ELit Lit                             -- ^ Literal
          | ETuple [Expr]                        -- ^ Tuple
          | EList [Expr]                         -- ^ List
          | ESett [Expr]                         -- ^ Set
          | ELam Pattern Expr                    -- ^ Lambda abstraction
          | EApp Expr Expr                       -- ^ Function application
          | EFix Expr                            -- ^ Fixpoint
          | ELet Pattern Expr Expr               -- ^ Let binding
          | ELetRd Pattern Expr Expr             -- ^ Rd binding
          | ELetBang Pattern Expr Expr           -- ^ Unpack linear binding
          | EBang Expr                           -- ^ Linearize
          | EIf Expr Expr Expr                   -- ^ Conditional
          | EMatch Expr [(Pattern, Expr, Expr)]  -- ^ Pattern match 
          | ENu (Name, Name) Expr                -- ^ Channel allocation
          | ERd Expr                             -- ^ Read from channel
          | EWr Expr Expr                        -- ^ Write to channel
          | EFork Expr Expr                      -- ^ Fork new process
          | EChoice Expr Expr                    -- ^ External choice
          | ERef Expr                            -- ^ Mutable reference
          | EGet Expr                            -- ^ Dereference
          | ESet Name Expr                       -- ^ Mutable Assignment
          | ESeq Expr Expr                       -- ^ Sequencing
          | EPrint Expr                          -- ^ Print
          | EError Expr                          -- ^ Throw error
          | EBin Binop Expr Expr                 -- ^ Binary expression
          | EUn Unop Expr                        -- ^ Unary expression
          | ECustom Name [Expr]                  -- ^ Custom data type
          deriving (Eq, Show)

-- | Literals in ILC.
data Lit = LInt Integer    -- ^ Integer literal
         | LBool Bool      -- ^ Boolean literal
         | LString String  -- ^ String literal
         | LUnit           -- ^ Unit literal
         deriving (Eq, Show)

-- | Built-in binary operators in ILC.
data Binop = Add     -- ^ Addition
           | Sub     -- ^ Subtraction
           | Mul     -- ^ Multiplication
           | Div     -- ^ Integer division
           | Mod     -- ^ Remainder
           | And     -- ^ Logical and
           | Or      -- ^ Logical or
           | Lt      -- ^ Less than
           | Gt      -- ^ Greater than
           | Leq     -- ^ Less than or equal to
           | Geq     -- ^ Greater than or equal to
           | Eql     -- ^ Equal to
           | Neq     -- ^ Not equal to
           | Cons    -- ^ Cons element to list
           | Concat  -- ^ List concatenation
           deriving (Eq, Show)

-- | Built-in unary operator in ILC.
data Unop = Not  -- ^ Logical not
  deriving (Eq, Show)

-- | Pattern match patterns in ILC.
data Pattern = PVar Name              -- ^ Variable pattern
             | PInt Integer           -- ^ Integer literal pattern
             | PBool Bool             -- ^ Boolean literal pattern
             | PString String         -- ^ String literal pattern
             | PUnit                  -- ^ Unit literal pattern
             | PWildcard              -- ^ Wildcard pattern
             | PTuple [Pattern]       -- ^ Tuple pattern
             | PList [Pattern]        -- ^ List pattern
             | PCons Pattern Pattern  -- ^ Cons pattern
             | PSet [Pattern]         -- ^ Set pattern
             | PCust Name [Pattern]   -- ^ Custom data type pattern
             deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Pretty printing
--------------------------------------------------------------------------------

instance Pretty Pattern where
  pretty (PVar x)      = text x
  pretty (PInt n)      = integer n
  pretty (PBool True)  = text "true"
  pretty (PBool False) = text "false"
  pretty (PString s)   = text s
  pretty PUnit         = text "()"
  pretty PWildcard     = text "_"
  pretty (PTuple ps)   = prettyTuple $ map pretty ps
  pretty (PList ps)    = prettyList ps
  pretty (PCons hd tl) = pretty hd <+> text ":" <+> pretty tl
  pretty (PSet ps)     = prettySet $ map pretty ps
  pretty (PCust x ps)  = text x <+> prettySpace (map pretty ps)
