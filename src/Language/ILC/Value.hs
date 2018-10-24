--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Value
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Defines ILC values.
--
--------------------------------------------------------------------------------

module Language.ILC.Value (
    Value(..)
  , TermEnv
  , emptyTmEnv
  , extendTmEnv
  , mergeTmEnv
  ) where

import Control.Concurrent
import Data.IORef
import qualified Data.Map.Strict as Map
import Text.PrettyPrint.ANSI.Leijen

import Language.ILC.Pretty
import Language.ILC.Syntax

-- | Values in ILC.
data Value = VInt Integer                        -- ^ Integer value
           | VBool Bool                          -- ^ Boolean value
           | VString String                      -- ^ String value
           | VList [Value]                       -- ^ List value
           | VSet [Value]                        -- ^ Set value
           | VTuple [Value]                      -- ^ Tuple value
           | VUnit                               -- ^ Unit value
           | VClosure (Maybe Name) TermEnv Expr  -- ^ Closure value
           | VRdChan Name (Chan Value)           -- ^ Read channel value
           | VWrChan Name (Chan Value)           -- ^ Write channel value
           | VRef (IORef Value)                  -- ^ Mutable reference value
           | VCust Name [Value]                  -- ^ Mutable reference value
           deriving (Eq, Show)

instance Show (IORef a) where
  show _ = "IORef"

instance Show (Chan a) where
  show _ = "Chan"

instance Pretty Value where
  pretty (VInt n)      = integer n
  pretty (VBool True)  = text "true"
  pretty (VBool False) = text "false"
  pretty (VString s)   = text s
  pretty (VList vs)    = prettyList vs
  pretty (VTuple vs)   = prettyTuple $ map pretty vs
  pretty (VSet vs)     = prettySet $ map pretty vs
  pretty VUnit         = text "()"
  pretty VClosure{}    = text "<closure>"
  pretty (VRdChan c _) = text "Rd" <+> text c
  pretty (VWrChan c _) = text "Wr" <+> text c
  pretty (VRef _)      = text "<ref>"
  pretty (VCust x [])  = text x
  pretty (VCust x vs)  = text x <+> prettySpace (map pretty vs)
  
-- | A map from names to values.
type TermEnv = Map.Map Name Value

-- | The empty term environment.
emptyTmEnv :: TermEnv
emptyTmEnv = Map.empty

-- | Extends the term environment with the given binding.
extendTmEnv :: TermEnv -> Name -> Value -> TermEnv
extendTmEnv env x v = Map.insert x v env

-- | Extends the term environment with the given binding.
mergeTmEnv :: TermEnv -> TermEnv -> TermEnv
mergeTmEnv env1 env2 = Map.union env1 env2
