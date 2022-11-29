{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
module UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Client.Common
    (handleStep
    ) where

import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Internal
import Data.Ix

handleStep :: forall uni fun s.
             (Ix fun, PrettyUni uni fun, GivenCekReqs uni fun s)
           => CekState uni fun
           -> CekM uni fun s (CekState uni fun)
handleStep = \case
        Computing !unbudgetedSteps ctx (Closure term env) -> computeCekStep unbudgetedSteps ctx (Closure term env)
        Returning !unbudgetedSteps ctx val -> returnCekStep unbudgetedSteps ctx val
        self@(Terminating _) -> pure self -- idempotent

