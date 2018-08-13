--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Pretty
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- Pretty printing functions.
--
--------------------------------------------------------------------------------

module Language.ILC.Pretty (
    ) where

import qualified Data.Map as Map
import Text.PrettyPrint (Doc, (<>), (<+>))
import qualified Text.PrettyPrint as PP

import Language.ILC.Eval
import Language.ILC.Infer
import Language.ILC.Syntax
import Language.ILC.Type


parensIf :: Bool -> Doc -> Doc
parensIf True = PP.parens
parensIf False = id

class Pretty p where
  ppr :: Int -> p -> Doc

instance Pretty Expr where
  ppr _ (ELit (LInt n)) = PP.text $ show n
  ppr _ (ELit (LString s)) = PP.text $ show s
  ppr _ (ELit (LBool b)) = PP.text $ show b
  ppr _ (ELit LUnit) = PP.text "()"
  ppr p (EIf e1 e2 e3) =
        PP.text "if"   <+> ppr p e1
    <+> PP.text "then" <+> ppr p e2
    <+> PP.text "else" <+> ppr p e3
  ppr _ _ = PP.text "expr"

ppexpr :: Expr -> String
ppexpr = PP.render . ppr 0

{-instance Show TypeError where
  show (UnificationFail a b) =
    concat ["Cannot unify types: \n\t", pptype a, "\nwith \n\t", pptype b]
  show (InfiniteType (TV a) b) =
    concat ["Cannot construct the infinite type: ", a, " = ", pptype b]
  show (Ambiguous cs) =
    concat ["Cannot not match expected type: '" ++ pptype a ++ "' with actual type: '" ++ pptype b ++ "'\n" | (a,b) <- cs]
  show (UnboundVariable a) = "Not in scope: " ++ a
  show (ParFail m1 m2) = 
    concat ["Cannot derive mode composition: " ++ ppmode m1 ++ " | " ++ ppmode m2]
  show (SeqFail m1 m2) =
    concat ["Cannot derive mode composition: " ++ ppmode m1 ++ " ; " ++ ppmode m2]
  show (ChoiceFail m1 m2) =
    concat ["Subexpressions of choice must be of mode R: Given ", ppmode m1 ++ " and " ++ ppmode m2]-}
