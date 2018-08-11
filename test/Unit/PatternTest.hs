module Unit.PatternTest (
    test_patternMatch
  ) where

import Text.Printf
import Test.Tasty
import Test.Tasty.HUnit

import Language.ILC.Eval
import Language.ILC.Syntax

test_patternMatch :: TestTree
test_patternMatch =
    testGroup "Unit.PatternTest" $ map f examples'
  where f (str, v, p, env) = testCase (printf "Match %s" str) $
                             assertEqual "" (getBinds p v) env
                             
examples' =
    [ ( "tuple w/ vars"
      , VTuple [VInt 1, VBool True]
      , PTuple [PVar "x", PVar "y"]
      , Just [("x", VInt 1), ("y", VBool True)]
      )
    , ( "nested tuple w/ vars"
      , VTuple [VInt 1, VTuple [VInt 2, VInt 3], VBool True]
      , PTuple [PVar "x", PTuple [PVar "y", PWildcard], PVar "z"]
      , Just [("x", VInt 1), ("y", VInt 2), ("z", VBool True)]
      )
    , ( "tuple w/ failure"
      , VTuple [VInt 1, VInt 2, VInt 3]
      , PTuple [PWildcard, PVar "x", PInt 4]
      , Nothing
      )
    , ( "tuple w/ wildcards"
      , VTuple [VInt 1, VInt 2, VInt 3]
      , PTuple [PWildcard, PWildcard, PWildcard]
      , Just []
      )
    , ( "cons success"
      , VList [VInt 1, VInt 2, VInt 3]
      , PCons (PVar "hd") (PVar "tl")
      , Just [("hd", VInt 1), ("tl", VList [VInt 2, VInt 3])]
      )
    , ( "cons success w/ nil list"
      , VList [VInt 1]
      , PCons (PVar "hd") (PList [])
      , Just [("hd", VInt 1)]
      )
    , ( "cons success w/ nil list 2"
      , VList [VInt 1]
      , PCons (PVar "hd") (PVar "tl")
      , Just [("hd", VInt 1), ("tl", VList [])]
      )
    , ( "cons fail"
      , VList [VInt 1, VInt 2]
      , PCons (PVar "hd") (PList [])
      , Nothing
      )
    , ( "cons fail on nil"
      , VList []
      , PCons (PVar "hd") (PVar "tl")
      , Nothing
      )
    , ( "double cons"
      , VList [VInt 1, VInt 2]
      , PCons (PVar "a") (PCons (PVar "b") (PVar "c"))
      , Just [("a", VInt 1), ("b", VInt 2), ("c", VList [])]
      )
    ]
