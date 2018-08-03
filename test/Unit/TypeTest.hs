module Unit.TypeTest
  (
    test_types
  ) where

import Text.Printf
import Test.Tasty
import Test.Tasty.HUnit

import Eval
import Infer (inferExpr)
import Parser
import Pretty
import Type (emptyTyEnv)

test_types = testGroup "Unit.TypeTest" $ map f examples
  where f (str, src, ty) = testCase (printf "Infer type of %s" str) $
                           assertEqual "" (infer src) ty
        infer src = case parser src of
            Left err          -> error "bad test"
            Right [(_, expr)] -> case inferExpr emptyTyEnv expr of
                                     Left err -> error "bad test"
                                     Right sc -> ppscheme sc

examples =
    [ ( "compose"
      , "let compose f g = lam x . f (g x)"
      , "\8704 a b c . (a -> b) -> (c -> a) -> c -> b")
    , ( "map"
      , "letrec map f lst = match lst with | [] => [] | x:xs => (f x) : (map f xs)"
      , "\8704 a b . (a -> b) -> [a] -> [b]")
    , ( "assoclist"
      , "let f x = match x with | (a,b):[] => a"
      , "\8704 a b . [(a,b)] -> a")
    ]
