{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ConstraintKinds #-}
module UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Debugger where

import Annotation
import UntypedPlutusCore
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Internal
import Universe.Core

import Data.RandomAccessList.Class qualified as Env
import Data.Word64Array.Word8 hiding (Index, toList)
import Control.Monad.State
import Control.Monad.Trans.Free
import Control.Lens hiding (Context)
import Prettyprinter
import Data.Sequence as Seq
import Data.Coerce
import GHC.Exts

-- usually it is a line, but let's treat more generally as a srcspan
newtype Breakpoint = Breakpoint { unBreakpoint :: SrcSpan }
    deriving newtype (Show, Pretty)

-- | The terms that we can debug
type DTerm uni fun = Term NamedDeBruijn uni fun SrcSpans

-- commands that the debugger can receive fromthe debug-client (tui,cli,test,etc)
data Cmd
  =
  -- MAYBE: have a Load DTerm command; would require an initial invalid debugstate, i.e.  Maybe DebugState
  Reload -- ^ reset back to start of initial term
  -- small and big steps
  | Step -- ^ step the cek once
  | Next -- ^ step over aka next
  | Finish -- ^ run to the end of current function
  | ContinueBreak -- ^ continue to the end or until breakpoint reached
  | ContinueIgnore -- ^ continue to the end by temporarily ignoring breakpoints
  -- breakpoints
  | BreakAdd Breakpoint -- ^ create a new breakpoint
  | BreakDel Word -- ^ delete a breakpoint by index no.
  | BreakDelAll -- ^ convenience function
  | BreakList -- ^ list breakpoints
  -- variables
  | Print NamedDeBruijn
  | PrintAll -- ^ all debruijn in the env
  | Discharge NamedDeBruijn -- ^ dischargeCekValue
  | DischargeAll -- ^ forall v in env . dischargeCekValue
  | DischargeControl -- ^ dischargeCekValEnv
  -- frames
  | FrameList -- ^ aka Backtrace
  | FrameFocus Word -- ^ switch to frame by index no.
  -- Q: Is exit really needed?
  -- Wouldn't it be simpler for the Client to just ignore/throw away the debugger computation?
  | Exit -- ^ exit button or sth else control-d

type ShowUniFun uni fun =
    ( uni `Everywhere` Show
    , Closed uni
    , GShow uni
    , Show fun
    )

data DebuggerState uni fun = DebuggerState
    { _dLoadedTerm :: DTerm uni fun -- it is only here so we can more easily Reload
    , _dCekState :: CekState uni fun
    , _dBreakpoints :: Seq Breakpoint
    , _dFocusedFrameIx :: Word
    }
makeLenses ''DebuggerState

-- | Given the debugger's state, have we reached a breakpoint?
atBreakpoint :: DebuggerState uni fun -> Bool
atBreakpoint newDState =
    (newDState ^. dBreakpoints) `contain`
    (newDState ^? dCekState . cekStateClosure . closureTerm . to termAnn) -- look at the SrcSpan of the Control term
  where
    -- FIXME: stub, implement this, could we use PlutusLedgerAPI.V1.Interval api for it?
    contain :: Seq Breakpoint -> Maybe SrcSpans -> Bool
    contain _bs = \case
        Nothing -> False
        Just _srcSpan -> False -- todo

-- | The debugger's suspension functor
data DebugF uni fun a
  = InputF (Cmd -> a) -- iteratee
  | LogF String a -- generator
  | StepF
      (CekState uni fun) -- ^ newState
      (CekState uni fun -> a) -- ^ newCensoredState to continue
  | UpdateTuiF (DebuggerState uni fun) a -- generator
  deriving stock Functor

-- | The monad that the debugger operates in: a state monad plus a free monad
type Debugging m uni fun =
    ( MonadState (DebuggerState uni fun) m
    , MonadFree (DebugF uni fun) m
    , ShowUniFun uni fun
    )

-- | Initial debugger state
initDebugState :: DTerm uni fun -> DebuggerState uni fun
initDebugState t = DebuggerState
    {
      _dLoadedTerm = t
    , _dCekState = inject t
    , _dBreakpoints = mempty
    , _dFocusedFrameIx = 0
    }
    where
      inject :: DTerm uni fun -> CekState uni fun
      inject = Computing (toWordArray 0) NoFrame . flip Closure Env.empty

-- | Entrypoint of the debugger
debugger :: (ShowUniFun uni fun, MonadFree (DebugF uni fun) m)
         => DTerm uni fun -> m ()
debugger = void . execStateT debugLoop . initDebugState

-- | Main work of the debugger in a loop
--
-- it should be tail recursive
debugLoop :: Debugging m uni fun => m ()
debugLoop = inputF >>= \case

    Reload -> do
        curState <- get
        let initState = initDebugState $ curState ^. dLoadedTerm -- reinit
            restoreBreakPoints = set dBreakpoints $ curState ^. dBreakpoints
        put $ restoreBreakPoints initState
        updateTuiF =<< get
        debugLoop

    -- one step
    Step -> stepUntil $ const True

    -- multi steps

    -- step until breakpoint or context-length is back the same
    Next -> do
        s <- use dCekState
        forMOf_ cekStateContext s $ \curContext ->
            stepUntil $ \newDState -> atBreakpoint newDState ||
                    case newDState ^? dCekState . cekStateContext of
                        Just newContext -> lenContext newContext <= lenContext curContext
                        Nothing -> True -- this cannot be the case but anyway

    -- step until breakpoint or context-length is smaller
    Finish -> do
        s <- use dCekState
        forMOf_ cekStateContext s $ \curContext ->
             stepUntil $ \newDState -> atBreakpoint newDState ||
                    case newDState ^? dCekState . cekStateContext of
                        Just newContext -> lenContext newContext < lenContext curContext -- strictly smaller
                        Nothing -> True -- this cannot be the case but anyway

    -- continue to the end or until breakpoint reached
    ContinueBreak -> stepUntil atBreakpoint

    -- continue to the end by ignoring breakpoints
    ContinueIgnore -> stepUntil $ const False

    -- breakpoints
    BreakAdd bp -> do
         dBreakpoints %= (bp Seq.<|)
         updateTuiF =<< get
         debugLoop

    BreakList -> do
        logF . show . pretty . toList =<< use dBreakpoints
        debugLoop

    BreakDel i -> do
        dBreakpoints %= Seq.deleteAt (fromIntegral i)
        updateTuiF =<< get
        debugLoop

    BreakDelAll -> do
        dBreakpoints .= mempty
        updateTuiF =<< get
        debugLoop

    -- print a cekvalue in focused env
    Print (NamedDeBruijn _ lookIx) -> do
        -- TODO: use focused frame
        s <- use dCekState
        forOf_ cekStateClosure s $ \(Closure _cTerm cEnv) ->
                logF $ show $ cEnv `Env.indexOne` coerce lookIx
        debugLoop

    -- print all cekvalues in focused env
    PrintAll -> do
        -- TODO: use focused frame
        s <- use dCekState
        forOf_ cekStateClosure s $ \(Closure _cTerm cEnv) ->
                logF $ show cEnv
        debugLoop

    Discharge (NamedDeBruijn _ lookIx) -> do
        -- same as print but discharges to term
        -- TODO: dedup
        -- TODO: use focused frame
        s <- use dCekState
        forOf_ cekStateClosure s $ \(Closure _cTerm cEnv) ->
                case cEnv `Env.indexOne` coerce lookIx of
                    Just v -> logF $ show $ dischargeCekValue v
                    Nothing -> pure ()
        debugLoop

    DischargeAll -> do
        -- same as printall but discharges to term
        -- TODO: dedup
        -- TODO: use focused frame
        s <- use dCekState
        forOf_ cekStateClosure s $ \(Closure _cTerm cEnv) ->
                logF $ show $ fmap dischargeCekValue $ toList cEnv
        debugLoop

    DischargeControl -> do
        -- TODO: dedup
        -- TODO: use focused frame
        s <- use dCekState
        forOf_ cekStateClosure s $ \(Closure cTerm cEnv) ->
                logF $ show $ dischargeCekValEnv cEnv cTerm
        debugLoop

    -- frames
    FrameList -> do
        s <- use dCekState
        forOf_ cekStateContext s $
            logF . show
        debugLoop

    FrameFocus i -> do
        dFocusedFrameIx .= i
        updateTuiF =<< get
        debugLoop

    Exit -> pure ()

-- | An action to step until a condition on the 'DebuggerState' is met
stepUntil :: Debugging m uni fun => (DebuggerState uni fun -> Bool) -> m ()
stepUntil cond = do
    -- MAYBE: add condition-runaway safeguard/watchdog with a user-confirmation?
    dState <- get
    newCekState <- stepF $ dState ^. dCekState
    let newDState = dState & dCekState .~ newCekState
    put newDState
    if has (dCekState . _Terminating) newDState
       then updateTuiF newDState -- break, done
       else if cond newDState
            then do
                updateTuiF newDState
                debugLoop
            else stepUntil cond

-- * boilerplate "suspension actions"
-- Being in 'Debugging' monad here is more constrained than necessary, but it's ok.
inputF :: Debugging m uni fun => m Cmd
inputF = liftF $ InputF id
logF :: Debugging m uni fun => String -> m ()
logF text = liftF $ LogF text ()
updateTuiF :: Debugging m uni fun => DebuggerState uni fun -> m ()
updateTuiF dState = liftF $ UpdateTuiF dState ()
stepF :: Debugging m uni fun => CekState uni fun -> m (CekState uni fun)
stepF yieldState = liftF $ StepF yieldState id

