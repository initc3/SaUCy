module Pretty where
{-    (
      ppexpr
    , ppval
    ) where-}

import qualified Data.Map as Map
import Text.PrettyPrint (Doc, (<>), (<+>))
import qualified Text.PrettyPrint as PP

import Eval
import Infer
import Syntax
import Type

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

instance Pretty Value where
    ppr _ (VInt n) = PP.text $ show n
    ppr _ (VBool True) = PP.text "true"
    ppr _ (VBool False) = PP.text "false"
    ppr _ (VString s) = PP.text $ show s
    ppr _ (VTag s) = PP.text s
    ppr p (VList vs) = PP.brackets $ ppList p vs
    ppr p (VSet vs) = PP.braces $ ppList p vs
    ppr p (VTuple vs) = PP.parens $ ppList p vs
    ppr _ VUnit = PP.text "()"
    ppr _ (VClosure _ _ _) = PP.text "closure"
    ppr p (VThunk _ e) = PP.text "thunk(" <> ppr p e <> PP.text ")"
    ppr _ (VChannel x _) = PP.text x
    ppr _ (VRef x) = PP.text $ show x

ppList p vs = PP.hcat $ PP.punctuate PP.comma $ map (ppr p) vs

ppexpr :: Expr -> String
ppexpr = PP.render . ppr 0

ppval :: Value -> String
ppval = PP.render . ppr 0

instance Pretty TVar where
  ppr _ (TV x) = PP.text x

instance Pretty Type where
  ppr p (TVar a) = ppr p a
  ppr _ (TCon a) = PP.text a
  ppr p (TArr a b) = parensIf (isArrow a) (ppr p a) <+> PP.text "->" <+> ppr p b
    where
      isArrow TArr {} = True
      isArrow _ = False
  ppr p (TList a) = PP.brackets $ ppr p a
  ppr p (TProd as) = PP.parens $ ppList p as
  ppr p (TSet a) = PP.braces $ ppr p a
  ppr p (TRef a) = PP.text "Ref" <+> ppr p a
  ppr p (TThunk a) = PP.text "Thunk" <+> ppr p a
  ppr p (TRdChan a) = PP.text "Rd" <+> ppr p a
  ppr p (TWrChan a) = PP.text "Wr" <+> ppr p a

instance Pretty Scheme where
  ppr p (Forall [] t) = ppr p t
  ppr p (Forall ts t) = PP.text "\x2200" <+> PP.hcat (PP.punctuate PP.space (map (ppr p) ts)) <+> PP.text "." <+> ppr p t

instance Pretty Mode where
  ppr _ MV = PP.text "V"
  ppr _ MR = PP.text "R"
  ppr _ MW = PP.text "W"

instance Show TypeError where
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
    concat ["Subexpressions of choice must be of mode R: Given ", ppmode m1 ++ " and " ++ ppmode m2]

ppscheme :: Scheme -> String
ppscheme = PP.render . ppr 0

ppschmode :: (Scheme, Mode) -> String
ppschmode (sc, m) = PP.render $ ppr 0 sc <+> PP.text "@" <+> ppr 0 m

pptype :: Type -> String
pptype = PP.render . ppr 0

ppmode :: Mode -> String
ppmode = PP.render . ppr 0

ppsignature :: (String, (Scheme, Mode)) -> String
ppsignature (a, schmode) = a ++ " :: " ++ ppschmode schmode

ppenv :: TypeEnv -> [String]
ppenv (TypeEnv env) = map ppsignature $ Map.toList env
