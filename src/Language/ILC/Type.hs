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
    Type(..)
  , LType(..)
  , simpty
  , simpFully
  , linearize
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
  , TML(..)
  ) where

import qualified Data.Map as Map
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Language.ILC.Mode
import Language.ILC.Pretty
import Language.ILC.Syntax

-- | Intuitionistic types.
-- TODO: Fully separate intuitionistic and linear types.
data Type = TVar TVar            -- ^ Type variable
          | TCon String          -- ^ Type constructor
          | TProd [Type]         -- ^ Product type
          | TArr Type Type Mode  -- ^ Arrow type
          | TList Type           -- ^ List type
          | TSet Type            -- ^ Set type
          | TRef Type            -- ^ Reference type
          | TWrChan Type         -- ^ Write channel type
          | TCust Type           -- ^ Custom data type
          | TLin LType           -- ^ Linear type
          | TUsed                -- ^ Used linear type
          deriving (Eq, Ord, Show)

-- | Linear types.
data LType = LVar TVar              -- ^ Linear type variable
           | LRdChan Type           -- ^ Read channel type
           | LArr LType LType Mode  -- ^ Lollipop type (linear arrows)
           | LTensor LType LType    -- ^ Tensor type (linear pairs)
           | LBang Type             -- ^ Intuitionistic type
           deriving (Eq, Ord, Show)

-- | Iteratively simplifies the modes in a type until it reaches a fixed point.
simpFully :: Type -> Type
simpFully ty = if ty == ty' then ty else simpFully ty'
  where ty' = case simpty ty of
                Nothing -> error "mode error"
                Just x -> x

-- | Simplifies modes in intuitionistic types.
simpty :: Type -> Maybe Type
simpty t@TVar{}       = Just t
simpty t@TCon{}       = Just t
simpty t@TUsed        = Just t
simpty (TArr t1 t2 m) = TArr    <$> simpty  t1 <*> simpty t2 <*> mcompose m
simpty (TList t)      = TList   <$> simpty  t
simpty (TProd ts)     = TProd   <$> sequence (map simpty ts)
simpty (TSet t)       = TSet    <$> simpty  t
simpty (TRef t)       = TRef    <$> simpty  t
simpty (TWrChan t)    = TWrChan <$> simpty  t
simpty (TCust t)      = TCust   <$> simpty  t
simpty (TLin l)       = TLin    <$> simplty l

-- | Simplifies modes in linear types.
simplty :: LType -> Maybe LType
simplty l@(LVar _)      = Just l
simplty (LRdChan t)     = LRdChan <$> simpty  t
simplty (LArr l1 l2 m)  = LArr    <$> simplty l1 <*> simplty l2 <*> mcompose m
simplty (LTensor l1 l2) = LTensor <$> simplty l1 <*> simplty l2
simplty (LBang t)       = LBang   <$> simpty  t

-- | Transforms an intuitionistic type into a linear type.
linearize :: Type -> LType
linearize (TVar a) = LVar a
linearize (TArr t1 t2 m) = LArr (linearize t1) (linearize t2) m
linearize (TLin l) = l
linearize t = LBang t

-- | Wraps intuitionistic types, linear types, and modes.
data TML = T Type
         | L LType
         | M Mode
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

instance Pretty Type where
  pretty (TVar a)    = pretty a
  pretty (TCon a)    = pretty a
  pretty (TArr a b V)  = maybeParens (isArrow a) (pretty a) <+> text "->"
                                                            <+> pretty b
      where
        isArrow TArr {} = True
        isArrow _       = False
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
  pretty (TWrChan a) = text "Wr" <+> pretty a
  pretty (TLin l) = pretty l
  pretty (TCust a)  = pretty a
  pretty TUsed = text "Used"

instance Pretty LType where
  pretty (LVar a) = pretty a
  pretty (LRdChan a) = text "Rd" <+> pretty a
  pretty (LArr a b V)  = maybeParens (isArrow a) (pretty a) <+> text "-o"
                                                            <+> pretty b
      where
        isArrow LArr {} = True
        isArrow _       = False
  pretty (LArr a b m)  = maybeParens (isArrow a) (pretty a) <+> text "-o@"
                                                            <>  pretty m
                                                            <+> pretty b
      where
        isArrow LArr {} = True
        isArrow _       = False
  pretty (LTensor a b)  = pretty a <> text "⊗" <> pretty b
  pretty (LBang a)    = text "!(" <> pretty a <> text ")"

instance Pretty Scheme where
  pretty (Forall [] t) = pretty t
  pretty (Forall ts t) = text "∀" <+> hsep (map pretty ts)
                                  <+> text "." <+> pretty t

prettySignature :: (String, Scheme) -> Doc
prettySignature (a, sc) = text a <+> text "::"
                                      <+> pretty sc

prettyTyEnv :: TypeEnv -> [String]
prettyTyEnv (TypeEnv env) = map (show . prettySignature) $ Map.toList env

instance Pretty TML where
  pretty (T t) = pretty t
  pretty (L l) = pretty l
  pretty (M m) = pretty m
