module Syntax where

type Name = String

-- | Expressions
data Expr
    = EVar Name
    | EImpVar Name
    | ELit Lit
    | ETuple [Expr]
    | EList [Expr]
    | ESet [Expr]
    | ELam Pattern Expr
    | EApp Expr Expr
    | EFix Expr
    | ELet Pattern Expr Expr
    | EIf Expr Expr Expr
    | EMatch Expr [(Pattern, Expr, Expr)]
    | ENu (Name, Name) Expr
    | ERd Expr
    | EWr Expr Expr
    | EFork Expr Expr
    | ERepl Expr
    | ERef Expr
    | EDeref Expr
    | EAssign Name Expr
    | ESeq Expr Expr
    | EBin Binop Expr Expr
    | EBinArith ABinop Expr Expr
    | EBinBool BBinop Expr Expr
    | EBinRel RBinop Expr Expr
    | EUn Unop Expr
    | EUnBool BUnop Expr
    deriving (Eq, Show)

-- | Literals
data Lit
    = LInt Integer
    | LBool Bool
    | LString String
    | LTag String
    | LUnit
    deriving (Eq, Show)

-- | Binary operators
data Binop
    = Cons
    | Concat
    deriving (Eq, Show)

-- | Arithmetic
data ABinop
    = Add
    | Sub
    | Mul
    | Div
    | Mod
    deriving (Eq, Show)

-- | Booleans
data BBinop
    = And
    | Or
    deriving (Eq, Show)

-- | Relations
data RBinop
    = Lt
    | Gt
    | Leq
    | Geq
    | Eql
    | Neq
    deriving (Eq, Show)

-- | Unary operators
data Unop
    = Thunk
    | Force
    | Print
    | Error
    deriving (Eq, Show)

-- | Booleans
data BUnop
    = Not
    deriving (Eq, Show)

-- | Patterns
data Pattern
    = PVar Name
    | PInt Integer
    | PBool Bool
    | PString String
    | PTag String
    | PUnit
    | PWildcard
    | PTuple [Pattern]
    | PList [Pattern]
    | PCons Pattern Pattern
    | PSet [Pattern]
    deriving (Eq, Show)

-- | Toplevel declarations
type Decl = (Name, Expr)

-- | Program with main expression
data Program = Program [Decl] Expr  -- TODO: Main
    deriving (Eq, Show)
