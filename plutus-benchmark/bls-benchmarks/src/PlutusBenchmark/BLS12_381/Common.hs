-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wno-name-shadowing #-}

{- | Approximations of the sort of computations involving BLS12-381 primitives
 that one might wish to perform on the chain.  Real on-chain code will have
 extra overhead, but these examples help to give us an idea of the sort of
 computation that can feasibly be carried out within the validation budget
 limits. -}
module PlutusBenchmark.BLS12_381.Common ( UProg
                                        , UTerm
                                        , checkGroth16Verify_Haskell
                                        , listOfSizedByteStrings
                                        , mkGroth16VerifyScript
                                        , mkHashAndAddG1Script
                                        , mkHashAndAddG2Script
                                        , mkPairingScript
                                        , mkUncompressAndAddG1Script
                                        , mkUncompressAndAddG2Script
                                        , toAnonDeBruijnProg
                                        )
where
import PlutusCore (DefaultFun, DefaultUni)
import PlutusTx qualified as Tx
import UntypedPlutusCore qualified as UPLC

import PlutusTx.Prelude as Tx hiding (sort, (*))

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Word (Word8)
import Hedgehog.Internal.Gen qualified as G
import Hedgehog.Internal.Range qualified as R
import System.IO.Unsafe (unsafePerformIO)
import Text.Printf (printf, PrintArg)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Read as TR

import qualified Prelude as Haskell
import Prelude (IO, fromIntegral, show, Integer)
import Data.Function ((&))
import Data.Bifunctor (bimap)
import Data.Bits
import GHC.Integer (andInteger, orInteger)
import Data.Either (rights)

-------------------------------- PLC stuff--------------------------------

type UTerm   = UPLC.Term    UPLC.NamedDeBruijn DefaultUni DefaultFun ()
type UProg   = UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
type UDBProg = UPLC.Program UPLC.DeBruijn      DefaultUni DefaultFun ()


compiledCodeToTerm
    :: Tx.CompiledCodeIn DefaultUni DefaultFun a -> UTerm
compiledCodeToTerm (Tx.getPlcNoAnn -> UPLC.Program _ _ body) = body

{- | Remove the textual names from a NamedDeBruijn program -}
toAnonDeBruijnProg :: UProg -> UDBProg
toAnonDeBruijnProg (UPLC.Program () ver body) =
    UPLC.Program () ver $ UPLC.termMapNames (\(UPLC.NamedDeBruijn _ ix) -> UPLC.DeBruijn ix) body

-- Create a list containing n bytestrings of length l.  This could be better.
listOfSizedByteStrings :: Integer -> Integer -> [ByteString]
listOfSizedByteStrings n l = unsafePerformIO . G.sample $
                             G.list (R.singleton $ fromIntegral n)
                                  (G.bytes (R.singleton $ fromIntegral l))

---------------- Examples ----------------

-- Hash some bytestrings onto G1 and add them all together

{-# INLINABLE hashAndAddG1 #-}
hashAndAddG1 :: [BuiltinByteString] -> BuiltinBLS12_381_G1_Element
hashAndAddG1 [] = error ()
hashAndAddG1 (p:ps) =
    go ps (Tx.bls12_381_G1_hashToGroup p)
    where go [] acc     = acc
          go (q:qs) acc = go qs $ Tx.bls12_381_G1_add (Tx.bls12_381_G1_hashToGroup q) acc

mkHashAndAddG1Script :: [ByteString] -> UProg
mkHashAndAddG1Script l =
    let points = map toBuiltin l
    in Tx.getPlcNoAnn $ $$(Tx.compile [|| hashAndAddG1 ||]) `Tx.unsafeApplyCode` Tx.liftCode points

-- Hash some bytestrings onto G2 and add them all together
{-# INLINABLE hashAndAddG2 #-}
hashAndAddG2 :: [BuiltinByteString] -> BuiltinBLS12_381_G2_Element
hashAndAddG2 [] = error ()
hashAndAddG2 (p:ps) =
    go ps (Tx.bls12_381_G2_hashToGroup p)
    where go [] acc     = acc
          go (q:qs) acc = go qs $ Tx.bls12_381_G2_add (Tx.bls12_381_G2_hashToGroup q) acc

mkHashAndAddG2Script :: [ByteString] -> UProg
mkHashAndAddG2Script l =
    let points = map toBuiltin l
    in Tx.getPlcNoAnn $ $$(Tx.compile [|| hashAndAddG2 ||]) `Tx.unsafeApplyCode` Tx.liftCode points

-- Uncompress a list of compressed G1 points and add them all together
{-# INLINABLE uncompressAndAddG1 #-}
uncompressAndAddG1 :: [BuiltinByteString] -> BuiltinBLS12_381_G1_Element
uncompressAndAddG1 [] = error ()
uncompressAndAddG1 (p:ps) =
    go ps (Tx.bls12_381_G1_uncompress p)
    where go [] acc     = acc
          go (q:qs) acc = go qs $ Tx.bls12_381_G1_add (Tx.bls12_381_G1_uncompress q) acc

mkUncompressAndAddG1Script :: [ByteString] -> UProg
mkUncompressAndAddG1Script l =
    let points = map (Tx.bls12_381_G1_compress . Tx.bls12_381_G1_hashToGroup . toBuiltin) l
    in Tx.getPlcNoAnn $ $$(Tx.compile [|| uncompressAndAddG1 ||]) `Tx.unsafeApplyCode` Tx.liftCode points


-- Check that point addition is commutative in G1
checkUncompressAndAddG1_Haskell :: Integer -> IO ()
checkUncompressAndAddG1_Haskell n =
    let l = listOfSizedByteStrings 100 n
        points = map (Tx.bls12_381_G1_compress . Tx.bls12_381_G1_hashToGroup . toBuiltin) l
        result1 = uncompressAndAddG1 points
        result2 = uncompressAndAddG1 (reverse points)
    in do
      printf "%s\n" (show result1)
      printf "%s\n" (show result2)

-- Uncompress a list of compressed G1 points and add them all together
{-# INLINABLE uncompressAndAddG2 #-}
uncompressAndAddG2 :: [BuiltinByteString] -> BuiltinBLS12_381_G2_Element
uncompressAndAddG2 [] = error ()
uncompressAndAddG2 (p:ps) =
    go ps (Tx.bls12_381_G2_uncompress p)
    where go [] acc     = acc
          go (q:qs) acc = go qs $ Tx.bls12_381_G2_add (Tx.bls12_381_G2_uncompress q) acc

mkUncompressAndAddG2Script :: [ByteString] -> UProg
mkUncompressAndAddG2Script l =
    let points = map (Tx.bls12_381_G2_compress . Tx.bls12_381_G2_hashToGroup . toBuiltin) l
    in Tx.getPlcNoAnn $ $$(Tx.compile [|| uncompressAndAddG2 ||]) `Tx.unsafeApplyCode` Tx.liftCode points

-- Check that point addition is commutative in G2
checkUncompressAndAddG2_Haskell :: Integer -> IO ()
checkUncompressAndAddG2_Haskell n =
    let l = listOfSizedByteStrings 100 n
        points = map (Tx.bls12_381_G2_compress . Tx.bls12_381_G2_hashToGroup . toBuiltin) l
        result1 = uncompressAndAddG2 points
        result2 = uncompressAndAddG2 (reverse points)
    in do
      printf "%s\n" (show result1)
      printf "%s\n" (show result2)

-- Pairing operations

-- Take two points p1 and p2 in G1 and two points q1 and q2 in G2, apply the
-- Miller loop to (p1,q1) and (p2,q2), and then call finalVerify on the results.
{-# INLINABLE runPairingFunctions #-}
runPairingFunctions
    :: Tx.BuiltinBLS12_381_G1_Element
    -> Tx.BuiltinBLS12_381_G2_Element
    -> Tx.BuiltinBLS12_381_G1_Element
    -> Tx.BuiltinBLS12_381_G2_Element
    -> Bool
runPairingFunctions p1 q1 p2 q2 =
    let r1 = Tx.bls12_381_millerLoop p1 q1
        r2 = Tx.bls12_381_millerLoop p2 q2
    in Tx.bls12_381_finalVerify r1 r2

mkPairingScript
    :: BuiltinBLS12_381_G1_Element
    -> BuiltinBLS12_381_G2_Element
    -> BuiltinBLS12_381_G1_Element
    -> BuiltinBLS12_381_G2_Element
    -> UProg
mkPairingScript p1 q1 p2 q2 =
    Tx.getPlcNoAnn $ $$(Tx.compile [|| runPairingFunctions ||])
          `Tx.unsafeApplyCode` Tx.liftCode p1
          `Tx.unsafeApplyCode` Tx.liftCode q1
          `Tx.unsafeApplyCode` Tx.liftCode p2
          `Tx.unsafeApplyCode` Tx.liftCode q2

---------------- Groth16 verification ----------------

{- | An example of the on-chain computation required for verification of a Groth16
 proof.  The data here is derived from
 https://github.com/achimcc/groth16-example/blob/main/src/lib.rs -}

-- Wrappers for compressed group elements for slightly better type safety
newtype CompressedG1Element = CompressedG1Element { g1 :: BuiltinByteString }
    deriving newtype (Tx.Lift DefaultUni)

mkG1Element :: [Word8] -> CompressedG1Element
mkG1Element = CompressedG1Element . toBuiltin . BS.pack

newtype CompressedG2Element = CompressedG2Element { g2 :: BuiltinByteString }
    deriving newtype (Tx.Lift DefaultUni)

mkG2Element :: [Word8] -> CompressedG2Element
mkG2Element = CompressedG2Element . toBuiltin . BS.pack

encode :: Bool -> Integer -> [Integer]
encode isEnc n = if isEnc
    then (head output `orInteger` 160) : tail output
    else output
  where
    output = Haskell.reverse (go 48 [] n)

    go :: Integer -> [Integer] -> Integer -> [Integer]
    go 0 accum _ = accum
    go n accum input = go (n - 1) (accum ++ [input `andInteger` 255]) (input `shiftR` 8)

convertPoint :: Integer -> Integer -> [Integer]
convertPoint c0 c1 = let
    first = encode False c0
    second = encode True c1
    in second ++ first

toHex :: (PrintArg a) => a -> Text
toHex = T.pack . printf "%02x"

decodeOctet :: Text -> Either Text Word8
decodeOctet = bimap T.pack fst . TR.hexadecimal

convertToBytes :: Integer -> [Word8]
convertToBytes n = rights $ fmap (decodeOctet . toHex) (encode True n)

convertPointToBytes :: Integer -> Integer -> [Word8]
convertPointToBytes c0 c1 = rights $ fmap (decodeOctet . toHex) (convertPoint c0 c1)

scalar :: Integer
scalar = 0x1884d0cbcc5947434e46d19b3e904e18a8ee8d0d39ce9d315f3b00e338c8f618

-- Lots of group elements for input to the computation

alpha :: CompressedG1Element
alpha = mkG1Element $ convertToBytes 3557877563291136986657043117612817616154740709440858987690286834315829414413651295601965769329845932803473125912357

beta :: CompressedG2Element
beta = mkG2Element $ convertPointToBytes 1722171496331625125777812376707130965331370548053284953071914592257116522245525268029676643271393210291759228103244 3022017802898741425014024462467599677353752356733138166404278068663667049699351068993535147538107053776425757378013

gamma :: CompressedG2Element
gamma = mkG2Element $ convertPointToBytes 2331306779749605636810031528148843292663586541733795709826198597851861268722146366515163565753375141778453989308061 3336038986994623917843766837155310956688319908504589027508132152311138529184415458071528393671877837856845223951393

delta :: CompressedG2Element
delta = mkG2Element $ convertPointToBytes 280533224129040289838080132234362809856919893766682650592808932373333127663370496475633533242023293743624394017813 3026861528938991719713251251174214006254413845075440560246773036117255575322484077560492664145409922533683563475429

gamma_abc_1 :: CompressedG1Element
gamma_abc_1 = mkG1Element $ convertToBytes 3688415316316149460558579589031964696522452673650524623401299212716598568768585916168561754657724484715787042428344

gamma_abc_2 :: CompressedG1Element
gamma_abc_2 = mkG1Element $ convertToBytes 446241548779621102578249766197336970893747898893149127573583161546030914678647174824114687931862085638020035789278

a :: CompressedG1Element
a = mkG1Element [ 0xa0, 0x5b, 0xe5, 0x0f, 0xab, 0x57, 0x95, 0xbb
                , 0x87, 0x84, 0x39, 0x3a, 0x50, 0x45, 0xf9, 0x87
                , 0x47, 0x17, 0x3a, 0xd2, 0x87, 0xf5, 0x5e, 0x21
                , 0x34, 0x71, 0xbd, 0x55, 0x97, 0x45, 0x55, 0x14
                , 0x52, 0x45, 0x3c, 0x4c, 0x3a, 0x39, 0xe7, 0xc8
                , 0x83, 0x10, 0x84, 0x9f, 0x3c, 0x7a, 0x1f, 0xc3 ]

b :: CompressedG2Element
b = mkG2Element [ 0xad, 0x63, 0x48, 0xb6, 0xb7, 0xb3, 0x4c, 0x86
                , 0xbf, 0x37, 0xa7, 0x48, 0xcd, 0x2d, 0x82, 0xa2
                , 0x50, 0xdf, 0xc6, 0x48, 0x46, 0x75, 0x66, 0x88
                , 0x25, 0xa1, 0x6f, 0x7d, 0xa6, 0xa0, 0x4d, 0x34
                , 0x24, 0x11, 0x3e, 0x32, 0x5c, 0xe7, 0x34, 0xec
                , 0x44, 0x95, 0x60, 0x82, 0xc0, 0xa0, 0x6e, 0x5f
                , 0x18, 0x68, 0xe1, 0xf1, 0xa6, 0xe5, 0x59, 0xb9
                , 0xfe, 0x81, 0xf1, 0xa9, 0x01, 0xf8, 0xa6, 0x34
                , 0x1b, 0x30, 0x1c, 0x45, 0xb2, 0x5d, 0x30, 0x80
                , 0xfb, 0xc5, 0x03, 0x93, 0x53, 0xd8, 0xf7, 0x1b
                , 0x55, 0x0b, 0x27, 0x4e, 0xc4, 0xc0, 0x7c, 0x70
                , 0xcd, 0x11, 0x53, 0x56, 0x2c, 0x31, 0x4c, 0x97 ]

c :: CompressedG1Element
c = mkG1Element [ 0xb5, 0x69, 0xcc, 0x49, 0x1b, 0x4d, 0xf0, 0x35
                , 0xcb, 0xf4, 0x9e, 0x95, 0x1f, 0xd4, 0xfe, 0x30
                , 0xaa, 0x82, 0x36, 0xb0, 0xe2, 0xaf, 0x68, 0xf4
                , 0xc1, 0x59, 0x2c, 0xd4, 0x0d, 0xeb, 0xeb, 0x71
                , 0x8a, 0xf3, 0x36, 0x39, 0xdb, 0x6b, 0xc1, 0xe2
                , 0xda, 0x9d, 0x98, 0xe5, 0x53, 0xe5, 0xea, 0xed ]

{-# INLINABLE groth16Verify #-}
groth16Verify
    :: BuiltinByteString  -- G1
    -> BuiltinByteString  -- G2
    -> BuiltinByteString  -- G2
    -> BuiltinByteString  -- G1
    -> BuiltinByteString  -- G1
    -> BuiltinByteString  -- G1
    -> BuiltinByteString  -- G1
    -> BuiltinByteString  -- G2
    -> BuiltinByteString  -- G1
    -> Integer
    -> Bool
groth16Verify (Tx.bls12_381_G1_uncompress -> alpha)
              (Tx.bls12_381_G2_uncompress -> beta)
              (Tx.bls12_381_G2_uncompress -> gamma)
              (Tx.bls12_381_G2_uncompress -> delta)
              (Tx.bls12_381_G1_uncompress -> abc1)
              (Tx.bls12_381_G1_uncompress -> abc2)
              (Tx.bls12_381_G1_uncompress -> a)
              (Tx.bls12_381_G2_uncompress -> b)
              (Tx.bls12_381_G1_uncompress -> c)
              s =
                  let l1    = Tx.bls12_381_millerLoop a b
                      l2    = Tx.bls12_381_millerLoop alpha beta
                      l3    = Tx.bls12_381_millerLoop c delta
                      p     = Tx.bls12_381_G1_add  abc1 (Tx.bls12_381_G1_scalarMul s abc2)
                      l4    = Tx.bls12_381_millerLoop p gamma
                      y     = Tx.bls12_381_mulMlResult l2 (Tx.bls12_381_mulMlResult l3 l4)
                  in Tx.bls12_381_finalVerify l1 y

{- | Make a UPLC script applying groth16Verify to the inputs.  Passing the
 newtype inputs increases the size and CPU cost slightly, so we unwrap them
 first.  This should return `True`. -}
mkGroth16VerifyScript :: UProg
mkGroth16VerifyScript =
    Tx.getPlcNoAnn $ $$(Tx.compile [|| groth16Verify ||])
           `Tx.unsafeApplyCode` (Tx.liftCode $ g1 alpha)
           `Tx.unsafeApplyCode` (Tx.liftCode $ g2 beta)
           `Tx.unsafeApplyCode` (Tx.liftCode $ g2 gamma)
           `Tx.unsafeApplyCode` (Tx.liftCode $ g2 delta)
           `Tx.unsafeApplyCode` (Tx.liftCode $ g1 gamma_abc_1)
           `Tx.unsafeApplyCode` (Tx.liftCode $ g1 gamma_abc_2)
           `Tx.unsafeApplyCode` (Tx.liftCode $ g1 a)
           `Tx.unsafeApplyCode` (Tx.liftCode $ g2 b)
           `Tx.unsafeApplyCode` (Tx.liftCode $ g1 c)
           `Tx.unsafeApplyCode` Tx.liftCode scalar

-- | Check that the Haskell version returns the correct result.
checkGroth16Verify_Haskell :: Bool
checkGroth16Verify_Haskell =
    groth16Verify (g1 alpha) (g2 beta) (g2 gamma) (g2 delta)
                      (g1 gamma_abc_1) (g1 gamma_abc_2) (g1 a) (g2 b) (g1 c) scalar

