module Unit.TypeTest (
    test_types
  ) where

import Text.Printf
import Test.Tasty
import Test.Tasty.HUnit

import Language.ILC.Eval
import Language.ILC.Infer (inferExpr)
import Language.ILC.Parser
--import Language.ILC.Pretty
import Language.ILC.Type (emptyTyEnv, prettySchmode)

test_types = testGroup "Unit.TypeTest" $ map f examples
  where f (str, src, ty) = testCase (printf "Infer type of %s" str) $
                           assertEqual "" (infer src) ty
        infer src = case parser src of
            Left err          -> error "bad test"
            Right [(_, expr)] -> case inferExpr emptyTyEnv expr of
                                     Left err -> "ill-typed"
                                     Right scm -> show $ prettySchmode scm

examples =
    [ ( "compose"
      , "let compose f g = lam x . f (g x)"
      , "∀ a b c . (a -> b) -> (c -> a) -> c -> b @ V")
    , ( "map"
      , "letrec map f lst = match lst with | [] => [] | x:xs => (f x) : (map f xs)"
      , "∀ a b . (a -> b) -> [a] -> [b] @ V")
    , ( "assoclist"
      , "let f x = match x with | (a,b):[] => a"
      , "∀ a b . [(a,b)] -> a @ V")
    , ( "typed chan"
      , "let f () = nu (rc, wc) . wr 1 -> wc |> let (_, rc) = rd rc in rc"
      , "Unit -> Rd Int @ W")
    , ( "simple read"
      , "let f () = nu c . rd c"
      , "∀ a . Unit -> (a,Rd a) @ R")
    , ( "simple write"
      , "let f () = nu c . wr 1 -> c'"
      , "Unit -> Unit @ W")
    , ( "ill-typed chan"
      , "let f () = nu (rc, wc) . wr 1 -> wc |> wr () -> wc |> rc"
      , "ill-typed")
    , ( "parallel write"
      , "let f () = nu (rc, wc) . wr 1 -> wc |> wr 1 -> wc"
      , "ill-typed")
    , ( "sequential write"
      , "let f () = nu (rc, wc) . wr 1 -> wc ; wr 1 -> wc"
      , "ill-typed")
    , ( "diff branch modes"
      , "nu (rc, wc) . match 1 with | _ => wr 1 -> wc | _ => ()"
      , "ill-typed")
    ]
