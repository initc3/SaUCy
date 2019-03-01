{-# OPTIONS_GHC -Wall  #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.TypeError
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Describes type errors and implements error messages.
--
--------------------------------------------------------------------------------

module Language.ILC.TypeError (
    TypeError(..)
  ) where

import Text.PrettyPrint.ANSI.Leijen

import Language.ILC.Syntax
import Language.ILC.Type

data TypeError = UnificationFail Type Type
               | InfiniteType TVar Type
               | UnboundVariable Name
               | Ambiguous [(Type, Type)]
               | UnificationMismatch [Type] [Type]
               | TypeFail String
               | LinearFail Name

instance Show TypeError where
  show = show . pretty
  
instance Pretty TypeError where
  pretty (UnificationFail a b) =
    hsep [ text "Cannot unify types:\n\t"
         , pretty a
         , text "\nwith\n\t"
         , pretty b
         ]
  
  pretty (InfiniteType (TV a) b) =
    hsep [ text "Cannot construct the infinite type:"
         , pretty a
         , text "="
         , pretty b
         ]
         
  pretty (Ambiguous cs) =
    hsep [ hsep [ text "Cannot match expected type:"
                , text "'" <> pretty a <> text "'"
                , text "with actual type:"
                , text "'" <> pretty b <> text "'\n"
                ] | (a, b) <- cs ]
         
  pretty (UnboundVariable a) = text "Not in scope:" <+> pretty a
  
  pretty (TypeFail s)  = text s
  
  pretty (LinearFail x)  = text "Linear read channel violation on variable" <+> text x

  pretty _           = text "Unimplemented error message"
