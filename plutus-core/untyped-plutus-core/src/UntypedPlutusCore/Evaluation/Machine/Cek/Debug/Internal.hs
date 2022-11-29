-- editorconfig-checker-disable-file
-- | The CEK machine.
-- The CEK machine relies on variables having non-equal 'Unique's whenever they have non-equal
-- string names. I.e. 'Unique's are used instead of string names. This is for efficiency reasons.
-- The CEK machines handles name capture by design.


{-# LANGUAGE BangPatterns             #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE DeriveAnyClass           #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE ImplicitParams           #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE NPlusKPatterns           #-}
{-# LANGUAGE NamedFieldPuns           #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE TemplateHaskell     #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Internal
    (module UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Internal
    , module UntypedPlutusCore.Evaluation.Machine.Cek.Internal
    )
    -- -- See Note [Compilation peculiarities].
    -- ( EvaluationResult(..)
    -- , CekValue(..)
    -- , CekUserError(..)
    -- , CekEvaluationException
    -- , CekBudgetSpender(..)
    -- , ExBudgetInfo(..)
    -- , ExBudgetMode(..)
    -- , CekEmitter
    -- , CekEmitterInfo(..)
    -- , EmitterMode(..)
    -- , CekM (..)
    -- , ErrorWithCause(..)
    -- , EvaluationError(..)
    -- , ExBudgetCategory(..)
    -- , StepKind(..)
    -- , PrettyUni
    -- , extractEvaluationResult
    -- , runCekDeBruijn
    -- , dischargeCekValue
    -- )
where

import ErrorCode
import PlutusPrelude

import UntypedPlutusCore.Core


import Data.RandomAccessList.Class qualified as Env
import Data.RandomAccessList.SkewBinary qualified as Env
import PlutusCore.Builtin
import PlutusCore.DeBruijn
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Evaluation.Result
import PlutusCore.Pretty

import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (CekMachineCosts (..))

import Control.Lens hiding (Context)
import Control.Lens.Review
import Control.Monad.Catch
import Control.Monad.Except
import Control.Monad.ST
import Control.Monad.ST.Unsafe
import Data.Array hiding (index)
import Data.DList (DList)
import Data.Hashable (Hashable)
import Data.Kind qualified as GHC
import Data.Semigroup (stimes)
import Data.Text (Text)
import Data.Word
import Data.Word64Array.Word8 hiding (Index)
import Prettyprinter
import Universe
import GHC.IO (stToIO, ioToST)

import UntypedPlutusCore.Evaluation.Machine.Cek.Internal hiding (spendBudgetCek, enterComputeCek, runCekDeBruijn)

-- ADDED

-- | Context is only available if we are not done (Terminating)
data Closure uni fun = Closure
    { _closureTerm :: Term NamedDeBruijn uni fun ()
    , _closureEnv :: CekValEnv uni fun
    }
makeLenses ''Closure

data CekState uni fun =
    -- the next state is computing
    Computing WordArray (Context uni fun) (Closure uni fun)
    -- the next state is returning
    | Returning WordArray (Context uni fun) (CekValue uni fun)
    -- evaluation finished
    | Terminating (Term NamedDeBruijn uni fun ())
makePrisms ''CekState

-- helpers
ioToCekM = CekM . ioToST
cekMToIO = stToIO . unCekM

cekStateContext :: Traversal' (CekState uni fun) (Context uni fun)
cekStateContext f = \case
    Computing w k c -> Computing w `flip` c <$> f k
    Returning w k v -> Returning w `flip` v <$> f k
    x -> pure x

-- | Closure is only available if we are Computing (not Returning, or Terminating)
cekStateClosure :: Traversal' (CekState uni fun) (Closure uni fun)
cekStateClosure f = \case
    Computing w k c -> Computing w k <$> f c
    x -> pure x

upContext :: Word -> Context uni fun -> Maybe (Context uni fun)
upContext 0 = Just
upContext n = \case
    FrameApplyFun _ k -> upContext (n-1) k
    FrameApplyArg _ _ k -> upContext (n-1) k
    FrameForce k -> upContext (n-1) k
    _ -> Nothing

lenContext :: Context uni fun -> Word
lenContext = go 0
    where
      go :: Word -> Context uni fun -> Word
      go n = \case
              FrameApplyFun _ k -> go (n+1) k
              FrameApplyArg _ _ k -> go (n+1) k
              FrameForce k -> go (n+1) k
              _ -> 0

-- | Spend the budget that has been accumulated for a number of machine steps.
spendAccumulatedBudget ::
    forall uni fun s . (GivenCekReqs uni fun s)
    => WordArray
    -> CekM uni fun s ()
spendAccumulatedBudget !unbudgetedSteps = iforWordArray unbudgetedSteps spend

spendBudgetCek :: GivenCekSpender uni fun s => ExBudgetCategory fun -> ExBudget -> CekM uni fun s ()
spendBudgetCek = let (CekBudgetSpender spent) = ?cekBudgetSpender in spent

-- Making this a definition of its own causes it to inline better than actually writing it inline,
-- for some reason.
-- Skip index 7, that's the total counter!
-- See Note [Structure of the step counter]
{-# INLINE spend #-}
spend :: forall uni fun s . (GivenCekReqs uni fun s)
    => Int
    -> Word8
    -> CekM uni fun s ()
spend !i !w = unless (i == 7) $ let kind = toEnum i in spendBudgetCek (BStep kind) (stimes w (cekStepCost ?cekCosts kind))

-- | Accumulate a step, and maybe spend the budget that has accumulated for a number of machine steps, but only if we've exceeded our slippage.
stepAndMaybeSpend ::
    forall uni fun s
    . (GivenCekReqs uni fun s)
    => StepKind
    -> WordArray
    -> CekM uni fun s WordArray
stepAndMaybeSpend !kind !unbudgetedSteps = do
    -- See Note [Structure of the step counter]
    -- This generates let-expressions in GHC Core, however all of them bind unboxed things and
    -- so they don't survive further compilation, see https://stackoverflow.com/a/14090277
    let !ix = fromIntegral $ fromEnum kind
        !unbudgetedSteps' = overIndex 7 (+1) $ overIndex ix (+1) unbudgetedSteps
        !unbudgetedStepsTotal = readArray unbudgetedSteps' 7
    -- There's no risk of overflow here, since we only ever increment the total
    -- steps by 1 and then check this condition.
    if unbudgetedStepsTotal >= ?cekSlippage
    then spendAccumulatedBudget unbudgetedSteps' >> pure (toWordArray 0)
    else pure unbudgetedSteps'

computeCekStep
    :: forall uni fun s
    . (Ix fun, PrettyUni uni fun, GivenCekReqs uni fun s)
    => WordArray
    -> Context uni fun
    -> Closure uni fun
    -> CekM uni fun s (CekState uni fun)
-- s ; ρ ▻ {L A}  ↦ s , {_ A} ; ρ ▻ L
computeCekStep !unbudgetedSteps !ctx (Closure (Var _ varName) !env) = do
    !unbudgetedSteps' <- stepAndMaybeSpend BVar unbudgetedSteps
    val <- lookupVarName varName env
    pure $ Returning unbudgetedSteps' ctx val
computeCekStep !unbudgetedSteps !ctx (Closure (Constant _ val) !_) = do
    !unbudgetedSteps' <- stepAndMaybeSpend BConst unbudgetedSteps
    pure $ Returning unbudgetedSteps' ctx (VCon val)
computeCekStep !unbudgetedSteps !ctx (Closure (LamAbs _ name body) !env) = do
    !unbudgetedSteps' <- stepAndMaybeSpend BLamAbs unbudgetedSteps
    pure $ Returning unbudgetedSteps' ctx (VLamAbs name body env)
computeCekStep !unbudgetedSteps !ctx (Closure (Delay _ body) !env) = do
    !unbudgetedSteps' <- stepAndMaybeSpend BDelay unbudgetedSteps
    pure $ Returning unbudgetedSteps' ctx (VDelay body env)
-- s ; ρ ▻ lam x L  ↦  s ◅ lam x (L , ρ)
computeCekStep !unbudgetedSteps !ctx (Closure (Force _ body) !env) = do
    !unbudgetedSteps' <- stepAndMaybeSpend BForce unbudgetedSteps
    pure $ Computing unbudgetedSteps' (FrameForce ctx) (Closure body env)
-- s ; ρ ▻ [L M]  ↦  s , [_ (M,ρ)]  ; ρ ▻ L
computeCekStep !unbudgetedSteps !ctx (Closure (Apply _ fun arg) !env) = do
    !unbudgetedSteps' <- stepAndMaybeSpend BApply unbudgetedSteps
    pure $ Computing unbudgetedSteps' (FrameApplyArg env arg ctx) (Closure fun env)
-- s ; ρ ▻ abs α L  ↦  s ◅ abs α (L , ρ)
-- s ; ρ ▻ con c  ↦  s ◅ con c
-- s ; ρ ▻ builtin bn  ↦  s ◅ builtin bn arity arity [] [] ρ
computeCekStep !unbudgetedSteps !ctx (Closure term@(Builtin _ bn) !_) = do
    !unbudgetedSteps' <- stepAndMaybeSpend BBuiltin unbudgetedSteps
    meaning <- lookupBuiltin bn ?cekRuntime
    -- The @term@ is a 'Builtin', so it's fully discharged.
    pure $ Returning unbudgetedSteps' ctx (VBuiltin bn term meaning)
-- s ; ρ ▻ error A  ↦  <> A
computeCekStep !_ !_ (Closure (Error _) !_) =
    throwing_ _EvaluationFailure

returnCekStep
    :: forall uni fun s
    . (PrettyUni uni fun, GivenCekReqs uni fun s)
    => WordArray
    -> Context uni fun
    -> CekValue uni fun
    -> CekM uni fun s (CekState uni fun)
--- Instantiate all the free variable of the resulting term in case there are any.
-- . ◅ V           ↦  [] V
returnCekStep !unbudgetedSteps NoFrame val = do
    spendAccumulatedBudget unbudgetedSteps
    pure $ Terminating $ dischargeCekValue val
-- s , {_ A} ◅ abs α M  ↦  s ; ρ ▻ M [ α / A ]*
returnCekStep !unbudgetedSteps (FrameForce ctx) fun = forceEvaluateStep unbudgetedSteps ctx fun
-- s , [_ (M,ρ)] ◅ V  ↦  s , [V _] ; ρ ▻ M
returnCekStep !unbudgetedSteps (FrameApplyArg argVarEnv arg ctx) fun =
    pure $ Computing unbudgetedSteps (FrameApplyFun fun ctx) (Closure arg argVarEnv)
-- s , [(lam x (M,ρ)) _] ◅ V  ↦  s ; ρ [ x  ↦  V ] ▻ M
-- FIXME: add rule for VBuiltin once it's in the specification.
returnCekStep !unbudgetedSteps (FrameApplyFun fun ctx) arg =
    applyEvaluateStep unbudgetedSteps ctx fun arg

-- | @force@ a term and proceed.
-- If v is a delay then compute the body of v;
-- if v is a builtin application then check that it's expecting a type argument,
-- and either calculate the builtin application or stick a 'Force' on top of its 'Term'
-- representation depending on whether the application is saturated or not,
-- if v is anything else, fail.
forceEvaluateStep
    :: forall uni fun s
    . (PrettyUni uni fun, GivenCekReqs uni fun s)
    => WordArray
    -> Context uni fun
    -> CekValue uni fun
    -> CekM uni fun s (CekState uni fun)
forceEvaluateStep !unbudgetedSteps !ctx (VDelay body env) =
    pure $ Computing unbudgetedSteps ctx (Closure body env)
forceEvaluateStep !unbudgetedSteps !ctx (VBuiltin fun term runtime) = do
    -- @term@ is fully discharged, and so @term'@ is, hence we can put it in a 'VBuiltin'.
    let term' = Force () term
    case runtime of
        -- It's only possible to force a builtin application if the builtin expects a type
        -- argument next.
        BuiltinExpectForce runtime' -> do
            -- We allow a type argument to appear last in the type of a built-in function,
            -- otherwise we could just assemble a 'VBuiltin' without trying to evaluate the
            -- application.
            res <- evalBuiltinApp fun term' runtime'
            pure $ Returning unbudgetedSteps ctx res
        _ ->
            throwingWithCause _MachineError BuiltinTermArgumentExpectedMachineError (Just term')
forceEvaluateStep !_ !_ val =
    throwingDischarged _MachineError NonPolymorphicInstantiationMachineError val

-- | Apply a function to an argument and proceed.
-- If the function is a lambda 'lam x ty body' then extend the environment with a binding of @v@
-- to x@ and call 'computeCek' on the body.
-- If the function is a builtin application then check that it's expecting a term argument,
-- and either calculate the builtin application or stick a 'Apply' on top of its 'Term'
-- representation depending on whether the application is saturated or not.
-- If v is anything else, fail.
applyEvaluateStep
    :: forall uni fun s
    . (PrettyUni uni fun, GivenCekReqs uni fun s)
    => WordArray
    -> Context uni fun
    -> CekValue uni fun   -- lhs of application
    -> CekValue uni fun   -- rhs of application
    -> CekM uni fun s (CekState uni fun)
applyEvaluateStep !unbudgetedSteps !ctx (VLamAbs _ body env) arg =
    pure $ Computing unbudgetedSteps ctx (Closure body (Env.cons arg env))
-- Annotating @f@ and @exF@ with bangs gave us some speed-up, but only until we added a bang to
-- 'VCon'. After that the bangs here were making things a tiny bit slower and so we removed them.
applyEvaluateStep !unbudgetedSteps !ctx (VBuiltin fun term runtime) arg = do
    let argTerm = dischargeCekValue arg
        -- @term@ and @argTerm@ are fully discharged, and so @term'@ is, hence we can put it
        -- in a 'VBuiltin'.
        term' = Apply () term argTerm
    case runtime of
        -- It's only possible to apply a builtin application if the builtin expects a term
        -- argument next.
        BuiltinExpectArgument f -> do
            res <- evalBuiltinApp fun term' $ f arg
            pure $ Returning unbudgetedSteps ctx res
        _ ->
            throwingWithCause _MachineError UnexpectedBuiltinTermArgumentMachineError (Just term')
applyEvaluateStep !_ !_ val _ =
    throwingDischarged _MachineError NonFunctionalApplicationMachineError val

-- See Note [Compilation peculiarities].
-- | Evaluate a term using the CEK machine and keep track of costing, logging is optional.
runCekDeBruijn
    :: (Ix fun, PrettyUni uni fun)
    => MachineParameters CekMachineCosts CekValue uni fun
    -> ExBudgetMode cost uni fun
    -> EmitterMode uni fun
    -> Term NamedDeBruijn uni fun ()
    -> (Either (CekEvaluationException NamedDeBruijn uni fun) (Term NamedDeBruijn uni fun ()), cost, [Text])
runCekDeBruijn params mode emitMode term =
    runCekM params mode emitMode $ do
        spendBudgetCek BStartup (cekStartupCost ?cekCosts)
        enterComputeCek NoFrame (Closure term Env.empty)

-- See Note [Compilation peculiarities].
-- | The entering point to the CEK machine's engine.
enterComputeCek
    :: forall uni fun s
    . (Ix fun, PrettyUni uni fun, GivenCekReqs uni fun s)
    => Context uni fun
    -> Closure uni fun
    -> CekM uni fun s (Term NamedDeBruijn uni fun ())
enterComputeCek ctx (Closure term env) = continue $ Computing (toWordArray 0) ctx (Closure term env)


continue :: forall uni fun s
    . (Ix fun, PrettyUni uni fun, GivenCekReqs uni fun s)
    => CekState uni fun
    -> CekM uni fun s (Term NamedDeBruijn uni fun ())
continue (Computing !unbudgetedSteps ctx (Closure term env)) = do
    state <- computeCekStep unbudgetedSteps ctx (Closure term env)
    continue state
continue (Returning !unbudgetedSteps ctx val) = do
    state <- returnCekStep unbudgetedSteps ctx val
    continue state
continue (Terminating term) = pure term
