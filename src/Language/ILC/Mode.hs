--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Mode
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Syntax of modes and mode composition.
--
--------------------------------------------------------------------------------

module Language.ILC.Mode (
    TVar(..)
  , Mode(..)
  , msimplify
  ) where

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Language.ILC.Pretty

-- | Type and mode variable
newtype TVar = TV String deriving (Eq, Ord, Show)

-- | Modes
data Mode = V  -- ^ Value mode
          | W  -- ^ Write mode
          | R  -- ^ Read mode
          | MVar TVar
          | MVarVR TVar
          | MSeq Mode Mode
          | MPar Mode Mode
          deriving (Eq, Ord, Show)

-- | Mode composition
msimplify :: Mode -> Maybe Mode
msimplify V            = Just V
msimplify W            = Just W
msimplify R            = Just R
msimplify m@(MVar a)   = Just m
msimplify m@(MVarVR a) = Just m
msimplify (MSeq V  m ) = msimplify m
msimplify (MSeq W  V ) = Just W
msimplify (MSeq R  m ) = Just R <* msimplify m
msimplify (MSeq W  R ) = Just W
msimplify (MSeq W  W ) = Nothing
msimplify (MSeq m1 m2) = MSeq <$> msimplify m1 <*> msimplify m2
msimplify (MPar W  V ) = Just W
msimplify (MPar V  W ) = Just W
msimplify (MPar W  R ) = Just W
msimplify (MPar R  W ) = Just W
msimplify (MPar R  R ) = Just R
msimplify (MPar V  R ) = Just R
msimplify (MPar R  V ) = Just V
msimplify (MPar W  W ) = Nothing
msimplify (MPar m1 m2) = MPar <$> msimplify m1 <*> msimplify m2

--------------------------------------------------------------------------------
-- | Pretty printing
--------------------------------------------------------------------------------

instance Pretty TVar where
  pretty (TV x) = text x

instance Pretty Mode where
  pretty V = text "V"
  pretty R = text "R"
  pretty W = text "W"
  pretty (MVar a) = pretty a
  pretty (MVarVR a) = pretty a <> text "∈{V,R}"
  pretty (MSeq a b) = text "(" <> pretty a <> text ";" <> pretty b <> text ")"
  pretty (MPar a b) = text "(" <> pretty a <> text "|" <> pretty b <> text ")"  
