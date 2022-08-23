{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE MultiWayIf        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusTx.Show (
    Show (..),
    ShowS,
    showString,
    showSpace,
    showCommaSpace,
    showParen,
    appPrec,
    appPrec1,
    deriveShow,
) where

import PlutusTx.Base
import PlutusTx.Bool
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Either
import PlutusTx.Foldable (foldl)
import PlutusTx.List
import PlutusTx.Maybe
import PlutusTx.Show.TH

instance Show Builtins.Integer where
    {-# INLINEABLE showsPrec #-}
    showsPrec _ n =
        showString (if n `Builtins.lessThanInteger` 0 then "-" else "")
            . foldr alg id (toDigits n)
      where
        toDigits :: Builtins.Integer -> [Builtins.Integer]
        toDigits m =
            let quotient = m `Builtins.quotientInteger` 10
                remainder = m `Builtins.remainderInteger` 10
                digit =
                    if remainder `Builtins.lessThanInteger` 0
                        then 0 `Builtins.subtractInteger` remainder
                        else remainder
             in if quotient `Builtins.equalsInteger` 0
                    then [digit]
                    else digit : toDigits quotient
        alg :: Builtins.Integer -> ShowS -> ShowS
        alg digit acc =
            acc
                . showString
                    ( if
                        | digit `Builtins.equalsInteger` 0 -> "0"
                        | digit `Builtins.equalsInteger` 1 -> "1"
                        | digit `Builtins.equalsInteger` 2 -> "2"
                        | digit `Builtins.equalsInteger` 3 -> "3"
                        | digit `Builtins.equalsInteger` 4 -> "4"
                        | digit `Builtins.equalsInteger` 5 -> "5"
                        | digit `Builtins.equalsInteger` 6 -> "6"
                        | digit `Builtins.equalsInteger` 7 -> "7"
                        | digit `Builtins.equalsInteger` 8 -> "8"
                        | digit `Builtins.equalsInteger` 9 -> "9"
                        | otherwise                        -> "<invalid digit>"
                    )

instance Show Builtins.BuiltinByteString where
    {-# INLINEABLE showsPrec #-}
    -- Base16-encode the ByteString and show the result.
    showsPrec _ s = foldl alg id [0 .. Builtins.subtractInteger (Builtins.lengthOfByteString s) 1]
      where
        showWord8 :: Builtins.Integer -> ShowS
        showWord8 x =
            toHex (x `Builtins.divideInteger` 16)
                . toHex (x `Builtins.modInteger` 16)
        toHex x =
            if
                | x `Builtins.lessThanEqualsInteger` 9 -> showsPrec 0 x
                | x `Builtins.equalsInteger` 10        -> showString "a"
                | x `Builtins.equalsInteger` 11        -> showString "b"
                | x `Builtins.equalsInteger` 12        -> showString "c"
                | x `Builtins.equalsInteger` 13        -> showString "d"
                | x `Builtins.equalsInteger` 14        -> showString "e"
                | x `Builtins.equalsInteger` 15        -> showString "f"
                | otherwise                            -> showString "<invalid byte>"
        alg :: ShowS -> Builtins.Integer -> ShowS
        alg acc i = acc . showWord8 (Builtins.indexByteString s i)

instance Show Builtins.BuiltinString where
    {-# INLINEABLE showsPrec #-}
    showsPrec _ s = showString "\"" . showString s . showString "\""

instance Show Builtins.BuiltinData where
    {-# INLINEABLE showsPrec #-}
    showsPrec p d = showsPrec p (Builtins.serialiseData d)

instance Show Bool where
    {-# INLINEABLE show #-}
    show b = if b then "True" else "False"

instance Show () where
    {-# INLINEABLE show #-}
    show () = "()"

-- It is possible to make it so that when `a` is a builtin type, `show (xs :: [a])`
-- is compiled into a single `showConstant` call, rathern than `length xs` calls.
-- To do so the plugin would need to try to solve the @uni `Contains` [a]@ constraint,
-- and branch based on whether it is solvable. But the complexity doesn't seem to
-- be worth it: the saving in budget is likely small, and on mainnet the trace messages
-- are often erased anyway.
--
-- Same for the `Show (a, b)` instance.
instance Show a => Show [a] where
    {-# INLINEABLE showsPrec #-}
    showsPrec _ = showList (showsPrec 0)

{-# INLINEABLE showList #-}
showList :: forall a. (a -> ShowS) -> [a] -> ShowS
showList showElem = \case
    [] -> showString "[]"
    x : xs ->
        showString "["
            . showElem x
            . foldl alg id xs
            . showString "]"
      where
        alg :: ShowS -> a -> ShowS
        alg acc a = acc . showString "," . showElem a

deriveShow ''(,)
deriveShow ''(,,)
deriveShow ''(,,,)
deriveShow ''(,,,,)
deriveShow ''(,,,,,)
deriveShow ''(,,,,,,)
deriveShow ''(,,,,,,,)
deriveShow ''(,,,,,,,,)
deriveShow ''(,,,,,,,,,)
deriveShow ''(,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,,,,,,,,,)
deriveShow ''Maybe
deriveShow ''Either
