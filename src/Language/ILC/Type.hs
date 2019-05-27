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
  , UType(..)  
  , IType(..)
  , AType(..)
  , SType(..)    
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
  , intersectTyEnv
  , clearAffineTyEnv
  , checkWrTok
  , rmWrTok  
  , prettySignature
  , prettyTyEnv
  ) where

import qualified Data.Map as Map
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Language.ILC.Pretty
import Language.ILC.Syntax

-- | Type and mode variable
newtype TVar = TV String deriving (Eq, Ord, Show)

data Type = IType IType
          | AType AType
          | UType UType
          deriving (Eq, Ord, Show)

data UType = UVar TVar
           | UIType IType
           | UAType AType           
           deriving (Eq, Ord, Show)

-- | Intuitionistic types.
data IType = IVar TVar            -- ^ Type variable
           | ICon String          -- ^ Type constructor
           | IProd [IType]        -- ^ Product type
           | IArr IType Type      -- ^ Arrow type
           | IArrW IType Type     -- ^ Arrow type           
           | IList IType          -- ^ List type
           | IWrChan SType        -- ^ Write channel type
           | ICust IType          -- ^ Custom data type
           | ISend SType
           deriving (Eq, Ord, Show)

-- | Affine types.
data AType = AVar TVar
           | ARdChan SType
           | AProd [AType]        -- ^ Product type
           | ABang IType
           | AArr AType Type      -- ^ Arrow type           
           deriving (Eq, Ord, Show)

-- | Sendable types.
data SType = SVar TVar            -- ^ Type variable
           | SProd [SType]        -- ^ Product type
           | SCon String          -- ^ Type constructor
           deriving (Eq, Ord, Show)

-- | Type scheme
data Scheme = Forall [TVar] Type deriving (Eq, Ord, Show)

-- | Primitive types
tyInt, tyBool, tyString, tyUnit :: IType
tyInt    = ISend $ SCon "Int"
tyBool   = ISend $ SCon "Bool"
tyString = ISend $ SCon "String"
tyUnit   = ISend $ SCon "Unit"

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

intersectTyEnv :: TypeEnv -> TypeEnv -> TypeEnv
intersectTyEnv (TypeEnv a) (TypeEnv b) = TypeEnv (Map.intersection a b)

clearAffineTyEnv :: TypeEnv -> TypeEnv
clearAffineTyEnv (TypeEnv a) = TypeEnv $ Map.filter isInt a
  where isInt (Forall _ IType{}) = True
        isInt (Forall _ AType{}) = False
        isInt (Forall _ UType{}) = False        

checkWrTok :: TypeEnv -> Bool
checkWrTok (TypeEnv env) =
  case Map.lookup "WrTok" env of
    Nothing -> False
    Just _  -> True

rmWrTok :: TypeEnv -> TypeEnv
rmWrTok (TypeEnv a) = TypeEnv $ Map.filterWithKey isWrTok a
  where isWrTok "WrTok" _ = False
        isWrTok _       _ = True

instance Monoid TypeEnv where
  mempty  = emptyTyEnv
  mappend = mergeTyEnv
    
--------------------------------------------------------------------------------
-- Pretty printing
--------------------------------------------------------------------------------

instance Pretty TVar where
  pretty (TV x) = text x

instance Pretty Type where
  pretty (IType a) = pretty a
  pretty (AType a) = pretty a
  pretty (UType a) = pretty a

instance Pretty UType where
  pretty (UVar a) = pretty a
  pretty (UIType a) = pretty a
  pretty (UAType a) = pretty a    

instance Pretty IType where
  pretty (IVar a)    = pretty a
  pretty (ICon a)    = pretty a
  pretty (IProd as)  = _prettyTuple as
  pretty (IArr a b)  = maybeParens (isArrow a) (pretty a) <+> text "->"
                                                          <+> pretty b
      where
        isArrow IArr {} = True
        isArrow _       = False
  pretty (IArrW a b)  = maybeParens (isArrow a) (pretty a) <+> text "-*"
                                                           <+> pretty b
      where
        isArrow IArrW {} = True
        isArrow _       = False        
  pretty (IList a)   = brackets $ pretty a
  pretty (IWrChan a) = text "Wr" <+> pretty a
  pretty (ICust a)  = pretty a
  pretty (ISend a)  = pretty a  

instance Pretty AType where
  pretty (AVar a)    = pretty a
  pretty (ARdChan a) = text "Rd" <+> pretty a
  pretty (AProd as)  = _prettyTuple as
  pretty (ABang a)    = text "!" <+> pretty a
  pretty (AArr a b)  = maybeParens (isArrow a) (pretty a) <+> text "-o"
                                                          <+> pretty b
      where
        isArrow AArr {} = True
        isArrow _       = False  

instance Pretty SType where
  pretty (SVar a)    = pretty a
  pretty (SProd as)  = _prettyTuple as
  pretty (SCon a)    = pretty a  

instance Pretty Scheme where
  pretty (Forall [] t) = pretty t
  pretty (Forall ts t) = text "∀" <+> hsep (map pretty ts)
                                  <+> text "." <+> pretty t  

prettySignature :: (String, Scheme) -> Doc
prettySignature (a, sc) = text a <+> text "::"
                                      <+> pretty sc

prettyTyEnv :: TypeEnv -> [String]
prettyTyEnv (TypeEnv env) = map (show . prettySignature) $ Map.toList env
