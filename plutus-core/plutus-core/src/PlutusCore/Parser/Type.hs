-- editorconfig-checker-disable-file
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module PlutusCore.Parser.Type where

import PlutusPrelude

import PlutusCore.Annotation
import PlutusCore.BLS12_381.G1 as BLS12_381.G1
import PlutusCore.BLS12_381.G2 as BLS12_381.G2
import PlutusCore.BLS12_381.GT as BLS12_381.GT
import PlutusCore.Core.Type
import PlutusCore.Data
import PlutusCore.Default
import PlutusCore.MkPlc (mkIterTyApp)
import PlutusCore.Name
import PlutusCore.Parser.ParserCommon

import Control.Monad
import Data.ByteString (ByteString)
import Data.Text (Text)
import Text.Megaparsec hiding (ParseError, State, many, parse, some)

-- | A PLC @Type@ to be parsed. ATM the parser only works
-- for types in the @DefaultUni@ with @DefaultFun@.
type PType = Type TyName DefaultUni SrcSpan

varType :: Parser PType
varType = withSpan $ \sp ->
    TyVar sp <$> tyName

funType :: Parser PType
funType = withSpan $ \sp ->
    inParens $ TyFun sp <$> (symbol "fun" *> pType) <*> pType

allType :: Parser PType
allType = withSpan $ \sp ->
    inParens $ TyForall sp <$> (symbol "all" *> trailingWhitespace tyName) <*> kind <*> pType

lamType :: Parser PType
lamType = withSpan $ \sp ->
    inParens $ TyLam sp <$> (symbol "lam" *> trailingWhitespace tyName) <*> kind <*> pType

ifixType :: Parser PType
ifixType = withSpan $ \sp ->
    inParens $ TyIFix sp <$> (symbol "ifix" *> pType) <*> pType

builtinType :: Parser PType
builtinType = withSpan $ \sp -> inParens $ do
    SomeTypeIn (Kinded uni) <- (symbol "con" *> defaultUni)
    pure $ TyBuiltin sp (SomeTypeIn uni)

appType :: Parser PType
appType = withSpan $ \sp -> inBrackets $ do
    fn   <- pType
    args <- some pType
    pure $ mkIterTyApp sp fn args

kind :: Parser (Kind SrcSpan)
kind = withSpan $ \sp ->
    let typeKind = Type sp <$ symbol "type"
        funKind = KindArrow sp <$> (symbol "fun" *> kind) <*> kind
     in inParens (typeKind <|> funKind)

-- | Parser for @PType@.
pType :: Parser PType
pType = choice $ map try
    [ funType
    , ifixType
    , allType
    , builtinType
    , lamType
    , appType
    , varType
    ]

-- | Parser for built-in type applications.
defaultUniApplication :: Parser (SomeTypeIn (Kinded DefaultUni))
defaultUniApplication = do
    -- Parse the head of the application.
    f <- defaultUni
    -- Parse the arguments.
    as <- many defaultUni
    -- Iteratively apply the head to the arguments checking that the kinds match and
    -- failing otherwise.
    foldM tryUniApply f as

-- | Parser for built-in types (the ones from 'DefaultUni' specifically).
--
-- 'Kinded' is needed for checking that a type function can be applied to its argument.
-- I.e. we do Plutus kind checking of builtin type applications during parsing, which is
-- unfortunate, but there's no way we could construct a 'DefaultUni' otherwise.
--
-- In case of kind error no sensible message is shown, only an overly general one:
--
-- >>> :set -XTypeApplications
-- >>> :set -XOverloadedStrings
-- >>> import PlutusCore.Error
-- >>> import PlutusCore.Quote
-- >>> let runP = putStrLn . either display display . runQuoteT . parseGen @ParserErrorBundle defaultUni
-- >>> runP "(list integer)"
-- (list integer)
-- >>> runP "(bool integer)"
-- test:1:14:
--   |
-- 1 | (bool integer)
--   |              ^
-- expecting "bool", "bytestring", "data", "integer", "list", "pair", "string", "unit", or '('
--
-- This is to be fixed.
--
-- One thing we could do to avoid doing kind checking during parsing is to parse into
--
--     data TextualUni a where
--         TextualUni :: TextualUni (Esc (Tree Text))
--
-- i.e. parse into @Tree Text@ and do the kind checking afterwards, but given that we'll still need
-- to do the kind checking of builtins regardless (even for UPLC), we don't win much by deferring
-- doing it.
defaultUni :: Parser (SomeTypeIn (Kinded DefaultUni))
defaultUni = choice $ map try
    [ trailingWhitespace (inParens defaultUniApplication)
    , someType @_ @Integer <$ symbol "integer"
    , someType @_ @ByteString <$ symbol "bytestring"
    , someType @_ @Text <$ symbol "string"
    , someType @_ @() <$ symbol "unit"
    , someType @_ @Bool <$ symbol "bool"
    , someType @_ @[] <$ symbol "list"
    , someType @_ @(,) <$ symbol "pair"
    , someType @_ @Data <$ symbol "data"
    , someType @_ @BLS12_381.G1.Element <$ symbol "BLS12_381G1Element"  -- FIXME !!!!  Upper/lower case? Better name?
    , someType @_ @BLS12_381.G2.Element <$ symbol "BLS12_381G2Element"
    , someType @_ @BLS12_381.GT.Element <$ symbol "BLS12_381GTElement"
    ]

tyName :: Parser TyName
tyName = TyName <$> name
