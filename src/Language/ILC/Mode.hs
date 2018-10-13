{-# OPTIONS_GHC -Wall  #-}
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
  , mcompose
  ) where

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

-- | Type and mode variable
newtype TVar = TV String deriving (Eq, Ord, Show)

-- | Modes
data Mode = V               -- ^ Value mode
          | W               -- ^ Write mode
          | R               -- ^ Read mode
          | MVar TVar       -- ^ Mode variable
          | MSeq Mode Mode  -- ^ Sequential mode composition
          | MPar Mode Mode  -- ^ Parallel mode composition
          deriving (Eq, Ord, Show)

-- | Mode compositions. The following mode compositions are not derivable, so
-- Nothing is returned: @m ; n => p@ and @m | n => p@.
mcompose :: Mode -> Maybe Mode
mcompose V            = Just V
mcompose W            = Just W
mcompose R            = Just R
mcompose m@MVar{}     = Just m
mcompose (MSeq W  V ) = Just W
mcompose (MSeq W  R ) = Just W
mcompose (MSeq R  m ) = Just R <* mcompose m
mcompose (MSeq V  m ) = mcompose m
mcompose (MSeq W  W ) = Nothing
mcompose (MSeq m1 m2) = MSeq <$> mcompose m1 <*> mcompose m2
mcompose (MPar W  V ) = Just W
mcompose (MPar V  W ) = Just W
mcompose (MPar W  R ) = Just W
mcompose (MPar R  W ) = Just W
mcompose (MPar R  V ) = Just R
mcompose (MPar V  R ) = Just R
mcompose (MPar R  R ) = Just R
mcompose (MPar V  V ) = Just V
mcompose (MPar W  W ) = Nothing
mcompose (MPar m1 m2) = MPar <$> mcompose m1 <*> mcompose m2

--------------------------------------------------------------------------------
-- Pretty printing
--------------------------------------------------------------------------------

instance Pretty TVar where
  pretty (TV x) = text x

instance Pretty Mode where
  pretty V          = text "V"
  pretty W          = text "W"
  pretty R          = text "R"
  pretty (MVar a)   = pretty a
  pretty (MSeq a b) = text "(" <> pretty a <> text ";" <> pretty b <> text ")"
  pretty (MPar a b) = text "(" <> pretty a <> text "|" <> pretty b <> text ")"  
