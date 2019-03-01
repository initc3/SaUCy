{-# OPTIONS_GHC -Wall  #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Type
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Defines the syntax and contexts for both intuitionistic and linear types.
--
--------------------------------------------------------------------------------

module Language.ILC.Type (
    TVar(..)
  , Type(..)
  , Scheme(..)
  , tyInt
  , tyBool
  , tyString
  , tyUnit
  , TypeEnv(..)
  , emptyTyEnv
  , removeTyEnv
  , extendTyEnv
  , lookupTyEnv
  , mergeTyEnv
  , prettySignature
  , prettyTyEnv
  ) where

import qualified Data.Map as Map
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Language.ILC.Pretty
import Language.ILC.Syntax

-- | Type and mode variable
newtype TVar = TV String deriving (Eq, Ord, Show)

-- | Intuitionistic types.
-- TODO: Fully separate intuitionistic and linear types.
data Type = TVar TVar            -- ^ Type variable
          | TCon String          -- ^ Type constructor
          | TProd [Type]         -- ^ Product type
          | TArr Type Type       -- ^ Arrow type
          | TList Type           -- ^ List type
          | TWrChan Type         -- ^ Write channel type
          | TRdChan Type         -- ^ Write channel type          
          | TCust Type           -- ^ Custom data type
          deriving (Eq, Ord, Show)

-- | Type scheme
data Scheme = Forall [TVar] Type deriving (Eq, Ord, Show)

-- | Primitive types
tyInt, tyBool, tyString, tyUnit :: Type
tyInt    = TCon "Int"
tyBool   = TCon "Bool"
tyString = TCon "String"
tyUnit   = TCon "Unit"

-- | Type environment
newtype TypeEnv = TypeEnv { types :: Map.Map Name Scheme }
  deriving (Eq, Show)

emptyTyEnv :: TypeEnv
emptyTyEnv = TypeEnv Map.empty

removeTyEnv :: TypeEnv -> Name -> TypeEnv
removeTyEnv (TypeEnv env) var = TypeEnv (Map.delete var env)

extendTyEnv :: TypeEnv -> (Name, Scheme) -> TypeEnv
extendTyEnv env (x, s) = env { types = Map.insert x s (types env) }

lookupTyEnv :: Name -> TypeEnv -> Maybe Scheme
lookupTyEnv key (TypeEnv tys) = Map.lookup key tys

mergeTyEnv :: TypeEnv -> TypeEnv -> TypeEnv
mergeTyEnv (TypeEnv a) (TypeEnv b) = TypeEnv (Map.union a b)

instance Monoid TypeEnv where
  mempty  = emptyTyEnv
  mappend = mergeTyEnv
    
--------------------------------------------------------------------------------
-- Pretty printing
--------------------------------------------------------------------------------

instance Pretty TVar where
  pretty (TV x) = text x

instance Pretty Type where
  pretty (TVar a)    = pretty a
  pretty (TCon a)    = pretty a
  pretty (TArr a b)  = maybeParens (isArrow a) (pretty a) <+> text "->"
                                                          <+> pretty b
      where
        isArrow TArr {} = True
        isArrow _       = False
  pretty (TList a)   = brackets $ pretty a
  pretty (TProd as)  = _prettyTuple as
  pretty (TWrChan a) = text "Wr" <+> pretty a
  pretty (TCust a)  = pretty a

instance Pretty Scheme where
  pretty (Forall [] t) = pretty t
  pretty (Forall ts t) = text "∀" <+> hsep (map pretty ts)
                                  <+> text "." <+> pretty t  

prettySignature :: (String, Scheme) -> Doc
prettySignature (a, sc) = text a <+> text "::"
                                      <+> pretty sc

prettyTyEnv :: TypeEnv -> [String]
prettyTyEnv (TypeEnv env) = map (show . prettySignature) $ Map.toList env
