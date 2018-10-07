module Unit.TypeTest (
    test_types
  ) where

import Text.Printf
import Test.Tasty
import Test.Tasty.HUnit

import Language.ILC.Decl
import Language.ILC.Eval
import Language.ILC.Infer (inferExpr)
import Language.ILC.Parser
import Language.ILC.Type (emptyTyEnv, prettySchmode)

test_types = testGroup "Unit.TypeTest" $ map f examples
  where f (str, src, ty) = testCase (printf "Infer type of %s" str) $
                           assertEqual "" (infer src) ty
        infer src = case parser src of
            Left err          -> error "bad test"
            Right [Decl _ expr] -> case inferExpr emptyTyEnv expr of
                                     Left err -> "ill-typed"
                                     Right scm -> show $ prettySchmode scm

examples :: [(String, String, String)]
examples =
    [ ( "compose"
      , "let compose f g = lam x . f (g x)"
      , "∀ a b c d . (a ->@c b) -> (d -> a) -> d ->@c b @ V")
    , ( "map"
      , "letrec map f lst = match lst with | [] => [] | x:xs => (f x) : (map f xs)"
      , "∀ a b . (a -> b) -> [a] -> [b] @ V")
    , ( "assoclist"
      , "let f x = match x with | (a,b):[] => a"
      , "∀ a b . [(a,b)] -> a @ V")
    {-, ( "typed chan"
      , "let f () = nu (rc, wc) . wr 1 -> wc |> let (_, rc) = rd rc in rc"
      , "Unit ->@W Rd Int @ V")-}
    , ( "simple read"
      , "let f () = nu c . rd c"
      , "∀ a . Unit ->@R (a,Rd a) @ V")
    , ( "simple write"
      , "let f () = nu c . wr 1 -> c'"
      , "Unit ->@W Unit @ V")
    , ( "ill-typed chan"
      , "let f () = nu (rc, wc) . wr 1 -> wc |> wr () -> wc |> rc"
      , "ill-typed")
    {-, ( "parallel write"
      , "let f () = nu (rc, wc) . wr 1 -> wc |> wr 1 -> wc"
      , "ill-typed")
    , ( "sequential write"
      , "let f () = nu (rc, wc) . wr 1 -> wc ; wr 1 -> wc"
      , "ill-typed")-}
    , ( "diff branch modes"
      , "nu (rc, wc) . match 1 with | _ => wr 1 -> wc | _ => ()"
      , "ill-typed")
    , ( "match branches good"
      , "let foo () = nu (r, w) . match 1 with | _ when print r ; true => 0 | _ => r ; 0"
      , "Unit -> Int @ V")
    , ( "match branches bad"
      , "let foo () = nu (r, w) . match 1 with | _ when print r ; true => 0 | _ => 0"
      , "ill-typed")
    ]
