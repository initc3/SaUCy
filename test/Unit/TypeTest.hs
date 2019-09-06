module Unit.TypeTest (
    test_types
  ) where

import Text.PrettyPrint.ANSI.Leijen
import Text.Printf
import Test.Tasty
import Test.Tasty.HUnit

import Language.ILC.Decl
import Language.ILC.Eval
import Language.ILC.Infer (inferExpr)
import Language.ILC.Parser.Toplevel
import Language.ILC.Type (emptyTyEnv)

test_types = testGroup "Unit.TypeTest" $ map f examples
  where f (str, src, ty) = testCase (printf "Infer type of %s" str) $
                           assertEqual "" (infer src) ty
        infer src = case parser src of
            Left err          -> error "bad test"
            Right [Decl _ expr] -> case inferExpr emptyTyEnv expr of
                                     Left err -> "ill-typed"
                                     Right sc -> show $ pretty sc

examples :: [(String, String, String)]
examples =
    [ ( "compose"
      , "let compose f g = lam x . f (g x)"
      , "∀ a b c . (a -> b) -> (c -> a) -> c -> b")
    , ( "map"
      , "letrec map f lst = match lst with | [] => [] | x:xs => (f x) : (map f xs)"
      , "∀ a b . (a -> b) -> [a] -> [b]")
    , ( "assoclist"
      , "let f x = match x with | (a,b):[] => a"
      , "∀ a b . [(a,b)] -> a")
--    , ( "simple read 1"
--      , "let f () = nu (r, w) . let (v, r) = rd r in v"
--      , "∀ a . !(Unit) -o@R !(a)")
--    , ( "simple read 2"
--      , "let f () = nu (r, w) . let (v, r) = rd r in r"
--      , "∀ a . !(Unit) -o@R Rd a")
--    , ( "simple write"
--      , "let f () = nu c . wr 1 -> c'"
--      , "Unit ->@W Unit")
    , ( "ill-typed chan"
      , "let f () = nu (rc, wc) . wr 1 -> wc |> wr () -> wc |> rc"
      , "ill-typed")
    , ( "parallel write"
      , "let f () = nu (rc, wc) . wr 1 -> wc |> wr 1 -> wc"
      , "ill-typed")
--    , ( "sequential write"
--      , "let f () = nu (rc, wc) . wr 1 -> wc ; wr 1 -> wc"
--      , "ill-typed")
    , ( "diff branch modes"
      , "nu (rc, wc) . match 1 with | _ => wr 1 -> wc | _ => ()"
      , "ill-typed")
--    , ( "match branches good"
--      , "let foo () = nu (r, w) . match 1 with | _ when print r ; true => 0 | _ => r ; 0"
--      , "Unit -> Int")
--    , ( "match branches bad"
--      , "let foo () = nu (r, w) . match 1 with | _ when print r ; true => 0 | _ => 0"
--      , "ill-typed")
--    , ( "seqsame"
--      , "let seqsame f x = f x ; f x"
--      , "∀ a b c . (a ->@c b) -> a ->@(c;c) b")
--    , ( "seqdiff"
--      , "let seqdiff f g x = f x ; g x"
--      , "∀ a b c d e . (a ->@c b) -> (a ->@e d) -> a ->@(c;e) d")
--    , ( "loop"
--      , "letrec loop c f = let (v, c) = rd c in let! v' = v in let! f' = f in f' v'; loop c f"
--      , "∀ a b c d . Rd a -o !(a ->@c b) -o@R d")
--    , ("linear read channel violation"
--      , "let foo () = nu (r, w) . let (v, x) = rd r in r"
--      , "ill-typed")
    ]
