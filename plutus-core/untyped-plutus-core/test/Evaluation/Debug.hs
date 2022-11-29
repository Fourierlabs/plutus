{-# LANGUAGE ImplicitParams #-}
module Evaluation.Debug
    ( test_debug
    ) where

import Test.Tasty
import Test.Tasty.Golden
import UntypedPlutusCore
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Client.Mock
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal (defaultSlippage)
import Data.ByteString.Lazy.Char8 qualified as BS

test_debug :: TestTree
test_debug =
    let ?cekRuntime = undefined
        ?cekEmitter = undefined
        ?cekBudgetSpender = undefined
        ?cekCosts = undefined
        ?cekSlippage = defaultSlippage
    in
    testGroup "debug" $
        fmap goldenVsDebug examples

goldenVsDebug (name,cmds,term) =
    goldenVsString name
    ("untyped-plutus-core/test/Evaluation/Debug/" ++ name ++ ".golden")
    (BS.pack . unlines <$> mock cmds term)

examples :: [(String, [Cmd], DTerm DefaultUni DefaultFun)]
examples = [ ("ex1", [], Error ())
           , ("ex2", [Exit], Error ())
           ]

