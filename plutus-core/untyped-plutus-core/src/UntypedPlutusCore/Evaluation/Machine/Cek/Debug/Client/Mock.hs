{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
module UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Client.Mock (mock, Cmd (..), DTerm (..)) where


import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Client.Common
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Internal
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Debugger
import Universe.Core

import Control.Monad.Trans.Free
import Control.Monad.ST (RealWorld)
import Control.Monad.RWS
import Data.Ix

type Mocking uni fun t m = ( MonadTrans t
                           -- the mock client feeds commands
                           , MonadReader [Cmd] (t m)
                           -- and writes to some string output (stdout/stderrr)
                           , MonadWriter [String] (t m)
                           , Ix fun, PrettyUni uni fun, GivenCekReqs uni fun RealWorld
                           )

mock :: ( Ix fun, PrettyUni uni fun, GivenCekReqs uni fun RealWorld
       , uni `Everywhere` Show, GShow uni, Show fun
       )
     => [Cmd] -- ^ commands to feed
     -> DTerm uni fun -- ^ term to debug
     -> IO [String] -- ^ mocking output
mock cmds = cekMToIO . runMocking . mockerInterprets . debugger
    where
      mockerInterprets = iterTM handle
      runMocking m = fmap snd $ execRWST m cmds ()

-- Interpretation of the mocker
-------------------------------

-- Note: the "ideal" way would be to write the mocking client also in coroutine-style (as a generator, etc)
-- and then pipe it to the debugger coroutine to create a larger coroutine which could then be interpreted as a whole:
-- but this could become complicated. See also https://themonadreader.files.wordpress.com/2011/10/issue19.pdf
-- Instead, we chose that the client is the actual "driver" / interpreter of the debugger.
handle :: ( Mocking uni fun t m
         , m ~ CekM uni fun RealWorld
         )
       => DebugF uni fun (t m ()) -> t m ()
handle = \case
  StepF prevState k -> lift (handleStep prevState) >>= k
  InputF k     -> handleInput k
  LogF text k  -> handleLog text >> k
  UpdateTuiF _ k -> k -- don't handle, just continue

-- more general as :: (MonadReader [Cmd] m, MonadWriter [String] m) => (Cmd -> m ()) -> m ()
handleInput :: Mocking uni fun t m => (Cmd -> t m ()) -> t m ()
handleInput k = do
    cmds <- ask
    case cmds of
        [] ->
            tell ["Early run out of commands"]
        (cmd:cmds') ->
            local (const cmds') $
                -- continue by feeding the next command to continuation
                k cmd

-- more general as handleLog :: (MonadWriter [String] m) => String -> m ()
handleLog :: Mocking uni fun t m => String -> t m ()
handleLog = tell . pure
