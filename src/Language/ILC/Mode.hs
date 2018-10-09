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
  , simpmo
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
          | MSeq Mode Mode
          | MPar Mode Mode
          deriving (Eq, Ord, Show)

-- | Mode composition
simpmo :: Mode -> Maybe Mode
simpmo V            = Just V
simpmo W            = Just W
simpmo R            = Just R
simpmo m@(MVar a)   = Just m
simpmo (MSeq W  V ) = Just W
simpmo (MSeq W  R ) = Just W
simpmo (MSeq R  m ) = Just R <* simpmo m
simpmo (MSeq V  m ) = simpmo m
simpmo (MSeq W  W ) = Nothing
simpmo (MSeq m1 m2) = MSeq <$> simpmo m1 <*> simpmo m2
simpmo (MPar W  V ) = Just W
simpmo (MPar W  R ) = Just W
simpmo (MPar R  m ) = simpmo m
simpmo (MPar V  m ) = simpmo m
simpmo (MPar W  W ) = Nothing
simpmo (MPar m1 m2) = MPar <$> simpmo m1 <*> simpmo m2

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
  pretty (MSeq a b) = text "(" <> pretty a <> text ";" <> pretty b <> text ")"
  pretty (MPar a b) = text "(" <> pretty a <> text "|" <> pretty b <> text ")"  
