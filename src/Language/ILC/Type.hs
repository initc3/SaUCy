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
  , msimplify
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
          | MVarVR TVar
          | MSeq Mode Mode
          | MPar Mode Mode
          deriving (Eq, Ord, Show)

msimplify :: Mode -> Maybe Mode
msimplify (MSeq V m)   = msimplify m
msimplify (MSeq W V)   = Just W
msimplify (MSeq R m)   = Just R <* msimplify m
msimplify (MSeq W R)   = Just W
msimplify (MSeq W W)   = Nothing
--msimplify (MSeq (MVar a) (MVar b)) = Just $ MSeq (MVarVR a) (MVarVR b)
msimplify (MSeq m1 m2) = MSeq <$> msimplify m1 <*> msimplify m2
msimplify (MPar W V)   = Just W
msimplify (MPar V W)   = Just W
msimplify (MPar W R)   = Just W
msimplify (MPar R W)   = Just W
msimplify (MPar R R)   = Just R
msimplify (MPar V R)   = Just R
msimplify (MPar R V)   = Just V
msimplify (MPar W W)   = Nothing
--msimplify (MPar (MVar a) (MVar b)) = Just $ MPar (MVarVR a) (MVarVR b)
msimplify (MPar m1 m2) = MPar <$> msimplify m1 <*> msimplify m2
msimplify V            = Just V
msimplify W            = Just W
msimplify R            = Just R
msimplify m@(MVar a)   = Just m
msimplify m@(MVarVR a) = Just m

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
  pretty (TThunk a)  = text "Thunk" <+> pretty a
  pretty (TRdChan a) = text "Rd" <+> pretty a
  pretty (TWrChan a) = text "Wr" <+> pretty a
  pretty TUsed = text "Used"

instance Pretty Mode where
  pretty V = text "V"
  pretty R = text "R"
  pretty W = text "W"
  pretty (MVar a) = pretty a
  pretty (MVarVR a) = pretty a <> text "∈{V,R}"
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
