module Unit.MatchTest (
    test_match
  ) where

import Data.Map.Strict (fromList)
import Text.Printf
import Test.Tasty
import Test.Tasty.HUnit

import Language.ILC.Eval
import Language.ILC.Match
import Language.ILC.Syntax
import Language.ILC.Value

test_match :: TestTree
test_match =
    testGroup "Unit.MatchTest" $ map f examples
  where f (str, v, p, env) = testCase (printf "Match %s" str) $
                             assertEqual "" (runMatch p v) env
                             
examples =
    [ ( "tuple w/ vars"
      , VTuple [VInt 1, VBool True]
      , PTuple [PVar "x", PVar "y"]
      , (Right (), fromList [("x", VInt 1), ("y", VBool True)])
      )
    , ( "nested tuple w/ vars"
      , VTuple [VInt 1, VTuple [VInt 2, VInt 3], VBool True]
      , PTuple [PVar "x", PTuple [PVar "y", PWildcard], PVar "z"]
      , (Right (), fromList [("x", VInt 1), ("y", VInt 2), ("z", VBool True)])
      )
    , ( "tuple w/ failure"
      , VTuple [VInt 1, VInt 2, VInt 3]
      , PTuple [PWildcard, PVar "x", PInt 4]
      , (Left (MatchFail (PInt 4) (VInt 3)), fromList [("x", VInt 2)])
      )
    , ( "tuple w/ wildcards"
      , VTuple [VInt 1, VInt 2, VInt 3]
      , PTuple [PWildcard, PWildcard, PWildcard]
      , (Right (), fromList [])
      )
    , ( "cons success"
      , VList [VInt 1, VInt 2, VInt 3]
      , PCons (PVar "hd") (PVar "tl")
      , (Right (), fromList [("hd", VInt 1), ("tl", VList [VInt 2, VInt 3])])
      )
    , ( "cons success w/ nil list"
      , VList [VInt 1]
      , PCons (PVar "hd") (PList [])
      , (Right (), fromList [("hd", VInt 1)])
      )
    , ( "cons success w/ nil list 2"
      , VList [VInt 1]
      , PCons (PVar "hd") (PVar "tl")
      , (Right (), fromList [("hd", VInt 1), ("tl", VList [])])
      )
    , ( "cons fail"
      , VList [VInt 1, VInt 2]
      , PCons (PVar "hd") (PList [])
      , (Left (MatchFail (PList []) (VList [VInt 2])), fromList [("hd", VInt 1)])
      )
    , ( "cons fail on nil"
      , VList []
      , PCons (PVar "hd") (PVar "tl")
      , (Left (MatchFail (PCons (PVar "hd") (PVar "tl")) (VList [])), fromList [])
      )
    , ( "double cons"
      , VList [VInt 1, VInt 2]
      , PCons (PVar "a") (PCons (PVar "b") (PVar "c"))
      , (Right (), fromList [("a", VInt 1), ("b", VInt 2), ("c", VList [])])
      )
    , ( "match cons with nil list"
      , VList []
      , PCons (PVar "hd") (PVar "tl")
      , (Left (MatchFail (PCons (PVar "hd") (PVar "tl")) (VList [])), fromList [])
      )
    ]
