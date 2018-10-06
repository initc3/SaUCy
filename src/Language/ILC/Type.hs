--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Type
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Types and modes.
--
--------------------------------------------------------------------------------

module Language.ILC.Type (
    TVar(..)
  , Type(..)
  , Mode(..)
  , Scheme(..)
  , tyInt
  , tyBool
  , tyString
  , tyTag
  , tyUnit
  , tyMsg
  , TypeEnv(..)
  , emptyTyEnv
  , removeTyEnv
  , extendTyEnv
  , lookupTyEnv
  , mergeTyEnv
  , prettySchmode
  , prettySignature
  , prettyTyEnv
  , TM(..)
  ) where

import qualified Data.Map as Map
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))    

import Language.ILC.Pretty
import Language.ILC.Syntax

-- | Type variable
newtype TVar = TV String deriving (Eq, Ord, Show)

-- | Types
data Type = TVar TVar            -- ^ Type variable
          | TCon String          -- ^ Type constructor
          | TArr Type Type Mode  -- ^ Arrow type
          | TList Type           -- ^ List type
          | TProd [Type]         -- ^ Product type
          | TSet Type            -- ^ Set type
          | TRef Type            -- ^ Reference type
          | TThunk Type          -- ^ Thunk type
          | TRdChan Type         -- ^ Read channel type
          | TWrChan Type         -- ^ Write channel type
          | TUsed                -- ^ Used linear type
          deriving (Eq, Ord, Show)

-- | Modes
data Mode = V  -- ^ Value mode
          | W  -- ^ Write mode
          | R  -- ^ Read mode
          | MVar TVar
          | MSeq Mode Mode
          | MPar Mode Mode
          deriving (Eq, Ord, Show)

-- | Type scheme
data Scheme = Forall [TVar] Type deriving (Eq, Ord, Show)

-- | Primitive types
tyInt, tyBool, tyString, tyTag, tyUnit, tyMsg :: Type
tyInt    = TCon "Int"
tyBool   = TCon "Bool"
tyString = TCon "String"
tyTag    = TCon "Tag"
tyUnit   = TCon "Unit"
tyMsg    = TCon "Msg"

-- | Type environment
newtype TypeEnv = TypeEnv { types :: Map.Map Name (Scheme, Mode) }
  deriving (Eq, Show)

emptyTyEnv :: TypeEnv
emptyTyEnv = TypeEnv Map.empty

removeTyEnv :: TypeEnv -> Name -> TypeEnv
removeTyEnv (TypeEnv env) var = TypeEnv (Map.delete var env)

extendTyEnv :: TypeEnv -> (Name, (Scheme, Mode)) -> TypeEnv
extendTyEnv env (x, s) = env { types = Map.insert x s (types env) }

lookupTyEnv :: Name -> TypeEnv -> Maybe (Scheme, Mode)
lookupTyEnv key (TypeEnv tys) = Map.lookup key tys

mergeTyEnv :: TypeEnv -> TypeEnv -> TypeEnv
mergeTyEnv (TypeEnv a) (TypeEnv b) = TypeEnv (Map.union a b)

instance Monoid TypeEnv where
  mempty  = emptyTyEnv
  mappend = mergeTyEnv
    
--------------------------------------------------------------------------------
-- Pretty printing

instance Pretty TVar where
  pretty (TV x) = text x

instance Pretty Type where
  pretty (TVar a)    = pretty a
  pretty (TCon a)    = pretty a
  pretty (TArr a b m)  = maybeParens (isArrow a) (pretty a) <+> text "->@"
                                                            <>  pretty m
                                                            <+> pretty b
      where
        isArrow TArr {} = True
        isArrow _       = False
  pretty (TList a)   = brackets $ pretty a
  pretty (TProd as)  = _prettyTuple as
  pretty (TSet a)    = pretty a
  pretty (TRef a)    = text "Ref" <+> pretty a
  pretty (TThunk a)  = text "Thunk" <+> pretty a
  pretty (TRdChan a) = text "Rd" <+> pretty a
  pretty (TWrChan a) = text "Wr" <+> pretty a
  pretty TUsed = text "Used"

instance Pretty Mode where
  pretty V = text "V"
  pretty R = text "R"
  pretty W = text "W"
  pretty (MVar a) = pretty a
  pretty (MSeq a b) = text "(" <> pretty a <> text ";" <> pretty b <> text ")"
  pretty (MPar a b) = text "(" <> pretty a <> text "|" <> pretty b <> text ")"

instance Pretty Scheme where
  pretty (Forall [] t) = pretty t
  pretty (Forall ts t) = text "∀" <+> hsep (map pretty ts)
                                  <+> text "." <+> pretty t

prettySchmode :: (Scheme, Mode) -> Doc
prettySchmode (sc, m) = pretty sc <+> text "@" <+> pretty m

prettySignature :: (String, (Scheme, Mode)) -> Doc
prettySignature (a, schmode) = text a <+> text "::"
                                      <+> prettySchmode schmode

prettyTyEnv :: TypeEnv -> [String]
prettyTyEnv (TypeEnv env) = map (show . prettySignature) $ Map.toList env

data TM = T Type
        | M Mode
        deriving (Eq, Ord, Show)

instance Pretty TM where
  pretty (T t) = pretty t
  pretty (M m) = pretty m
