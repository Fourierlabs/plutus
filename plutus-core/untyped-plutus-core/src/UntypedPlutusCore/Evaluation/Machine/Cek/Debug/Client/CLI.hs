{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
module UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Client.CLI where

import UntypedPlutusCore
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Client.Common
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Internal
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Debugger

import Control.Monad.Trans.Free
import Control.Monad.ST (RealWorld)
import Data.Ix

cliMain ::  forall uni fun
          . (ShowUniFun uni fun, Ix fun, PrettyUni uni fun, GivenCekReqs uni fun RealWorld)
          => DTerm uni fun
          -> IO ()
cliMain = cekMToIO . iterT handle . debugger

-- Peel off one layer
handle ::  forall uni fun m a
        . (m ~ CekM uni fun RealWorld,
          Ix fun, PrettyUni uni fun, GivenCekReqs uni fun RealWorld)
        => DebugF uni fun (m a)  -> m a
handle = \case
    StepF prevState k -> handleStep prevState >>= k
    InputF k -> handleInput >>= k
    LogF text k -> handleLog text >> k
    UpdateTuiF _ds k -> k -- TODO: implement
  where

    handleInput :: CekM uni fun RealWorld Cmd
    handleInput = read <$> ioToCekM getLine

    handleLog :: String -> CekM uni fun RealWorld ()
    handleLog = ioToCekM . putStrLn


-- FIXME: stub to "read" commands
instance Read Cmd
instance Read (Term NamedDeBruijn uni fun ())
instance Read NamedDeBruijn

