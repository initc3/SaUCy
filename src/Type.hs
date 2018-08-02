module Type where

import Syntax

import Data.Monoid
import qualified Data.Map as Map

newtype TVar = TV String
  deriving (Show, Eq, Ord)

data Type
    = TVar TVar
    | TCon String
    | TArr Type Type
    | TList Type
    | TProd [Type]
    | TSet Type
    | TRef Type
    | TThunk Type
    deriving (Show, Eq, Ord)

infixr `TArr`

data Scheme = Forall [TVar] Type
    deriving (Show, Eq, Ord)

tyInt, tyBool, tyString, tyTag, tyUnit :: Type
tyInt  = TCon "Int"
tyBool = TCon "Bool"
tyString = TCon "String"
tyTag = TCon "Tag"
tyUnit = TCon "Unit"
tyChan = TCon "Chan" -- TODO: Typed channels

newtype TypeEnv = TypeEnv { types :: Map.Map Name Scheme }
    deriving (Eq, Show)

emptyTyEnv :: TypeEnv
emptyTyEnv = TypeEnv Map.empty

remove :: TypeEnv -> Name -> TypeEnv
remove (TypeEnv env) var = TypeEnv (Map.delete var env)

extend :: TypeEnv -> (Name, Scheme) -> TypeEnv
extend env (x, s) = env { types = Map.insert x s (types env) }

lookup :: Name -> TypeEnv -> Maybe Scheme
lookup key (TypeEnv tys) = Map.lookup key tys

merge :: TypeEnv -> TypeEnv -> TypeEnv
merge (TypeEnv a) (TypeEnv b) = TypeEnv (Map.union a b)

instance Monoid TypeEnv where
    mempty = emptyTyEnv
    mappend = merge
