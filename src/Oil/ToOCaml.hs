{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Copyright: (c) 2022-2023 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Translate OIL to OCaml.
--
-- We simply pretty print the syntax tree to OCaml, without relying on any fancy
-- libraries. The translation is almost one-to-one, with some discrepancies that
-- we have to deal with:
--
--   - Naming: OCaml has its own naming rules regarding constructors, types and
--     functions, although it is pretty close to the naming rules in Taype and
--     Oil.
--
--   - ADT: OCaml constructor takes only one parameter, so we have to translate
--     a contructor application's multiple parameters into a tuple.
--
--   - (Mutual) recursion: we need to explicitly tell OCaml which functions are
--     (mutually) recursive.
--
-- We are being sloppy about naming at the moment, so there might be name
-- crashes. This can be easily solved by a more careful renaming scheme, but we
-- choose to not worry about it for simplicity and readability.
--
-- We try to reuse the definitions in OCaml, such as boolean and pair.
module Oil.ToOCaml (toOCaml) where

import Data.Char
import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (lookup)
import Data.Text qualified as T
import Oil.Syntax
import Taype.Common
import Taype.Cute
import Taype.Name
import Taype.Plate
import Taype.Prelude
import Prelude hiding (group)

----------------------------------------------------------------
-- Translating expressions and types

-- | Translate an OIL expression to OCaml expression.
toOCamlExpr :: Expr Text -> CuteM Doc
toOCamlExpr V {..} = cute name
toOCamlExpr GV {ref = isBuiltinExprName -> Just ref} = cute ref
toOCamlExpr GV {..} = cute $ toValidName ref
toOCamlExpr ILit {..} = cute iLit
toOCamlExpr e@Lam {} = toOCamlLam False e
toOCamlExpr
  e@App
    { fn = GV (isBuiltinExprName -> Just ref),
      args = [left, right]
    }
    | isInfix ref = do
        leftDoc <- cuteSubDoc e left <$> toOCamlExpr left
        rightDoc <- cuteSubDoc e right <$> toOCamlExpr right
        return $ cuteInfixDoc ref leftDoc rightDoc
-- Use OCaml's pair.
toOCamlExpr App {fn = GV "(,)", args = [left, right]} = do
  leftDoc <- toOCamlExpr left
  rightDoc <- toOCamlExpr right
  return $ cutePairDoc PublicP leftDoc rightDoc
toOCamlExpr
  App
    { fn = GV (isBuiltinExprName -> Just ref),
      ..
    } = toOCamlApp_ (pretty ref) args
toOCamlExpr App {fn = GV {..}, ..}
  | isCtor ref =
      let fnDoc = pretty ref
       in case args of
            [] -> return fnDoc
            [_] -> toOCamlApp_ fnDoc args
            _ -> do
              argDocs <- mapM toOCamlExpr args
              return $ hang $ fnDoc <> sep1 (toOCamlTuple argDocs)
toOCamlExpr App {..} = toOCamlApp fn args
toOCamlExpr Let {..} = do
  x <- toValidName <$> freshNameOrBinder binder
  rhsDoc <- toOCamlExpr rhs
  bodyDoc <- toOCamlExpr $ instantiateName x bnd
  return $ toOCamlLet (pretty x) rhsDoc bodyDoc
-- Use if conditional in OCaml for pattern matching on boolean.
toOCamlExpr
  Match
    { alts =
        [ MatchAlt {ctor = "False", binders = [], bnd = rBnd},
          MatchAlt {ctor = "True", binders = [], bnd = lBnd}
          ],
      ..
    } = do
    (_, left) <- unbindManyNamesOrBinders [] lBnd
    (_, right) <- unbindManyNamesOrBinders [] rBnd
    condDoc <- toOCamlExpr cond
    leftDoc <- toOCamlExpr left
    rightDoc <- toOCamlExpr right
    return $ cuteIteDoc PublicL condDoc leftDoc rightDoc
toOCamlExpr Match {alts = [MatchAlt {ctor = "(,)", ..}], ..} = do
  xs <- toValidName <<$>> mapM freshNameOrBinder binders
  case xs of
    [xl, xr] -> do
      condDoc <- toOCamlExpr cond
      bodyDoc <- toOCamlExpr $ instantiateName xs bnd
      return $
        toOCamlLet
          (group $ toOCamlTuple [pretty xl, pretty xr])
          condDoc
          bodyDoc
    _ -> oops "Binder number does not match"
toOCamlExpr Match {..} = do
  condDoc <- toOCamlExpr cond
  altDocs <- mapM goAltDoc alts
  return $
    align $
      "begin"
        <+> "match"
        <+> condDoc
        <+> "with"
          <> foldMap (\altDoc -> hardline <> pipe <+> altDoc) altDocs
        </> "end"
  where
    goAltDoc MatchAlt {..} = do
      xs <- toValidName <<$>> mapM freshNameOrBinder binders
      bodyDoc <- toOCamlExpr $ instantiateName xs bnd
      return $
        hang $
          pretty ctor
            <> ( case xs of
                   [] -> ""
                   [x] -> space <> pretty x
                   _ ->
                     sep1
                       ( parens $
                           align $
                             sepWith (comma <> line) (pretty <$> xs)
                       )
               )
            <+> "->" <> sep1 bodyDoc

-- | Translate an OIL type to OCaml type.
toOCamlTy :: Ty -> CuteM Doc
toOCamlTy TInt = "int"
toOCamlTy OArray = cute $ toValidName aName
toOCamlTy e@Arrow {..} = do
  domDoc <- cuteSubDoc e dom <$> toOCamlTy dom
  codDoc <- toOCamlTy cod
  return $ group domDoc <+> "->" <> line <> codDoc
toOCamlTy
  t@TApp
    { tctor = isBuiltinTyName -> Just tctor,
      args = [left, right]
    } | isInfix tctor = do
    leftDoc <- cuteSubDoc t left <$> toOCamlTy left
    rightDoc <- cuteSubDoc t right <$> toOCamlTy right
    return $ cuteInfixDoc tctor leftDoc rightDoc
toOCamlTy TApp {..} = do
  let tctor' = fromMaybe (toValidName tctor) $ isBuiltinTyName tctor
  argsDoc <- toOCamlTyArgs args
  return $ argsDoc <> pretty tctor'

----------------------------------------------------------------
-- Translate definitions

-- | Translate an OIL program into OCaml.
--
-- The generated file contains a OCaml functor @M@ parameterized by a driver
-- module implementing the cryptography primitives.
--
-- The generated OCaml program is roughly structured as follow.
--
-- @
-- (* This file is generated by the taype compiler. *)
-- module M (Driver : Taype_driver.S) = struct
--   open Driver
--   ... mainOil ...
--   module Conceal = struct
--     open Plaintext
--     ... concealOil ...
--     include Driver.Conceal
--     let s_ = s
--     let s k x = (k, obliv_array_conceal_with (s_ k) x)
--     let s_for k party = (k, obliv_array_new_for party (oadt k))
--   end
--   module Reveal = struct
--     open Plaintext
--     open Plaintext.Reveal
--     ... revealOil ...
--     include Driver.Reveal
--     let r_ = r
--     let r (k, a) = obliv_array_reveal_with (r_ k) a
--   end
-- end
-- @
toOCaml :: Options -> Program -> Doc
toOCaml options Program {..} =
  hdDoc <> mainDoc <> hardline
  where
    go = toOCamlDefs options
    hdDoc = "(* This file is generated by the taype compiler. *)" <> hardline2
    mainDoc =
      modDoc "M (Driver : Taype_driver.S)" $
        "open Driver"
          <//> go mainDefs
          <//> concealDoc
          <//> revealDoc
    -- Reexport functions in the Conceal and Reveal module.
    concealDoc =
      modDoc "Conceal" $
        "open Plaintext"
          <//> go concealDefs
          <//> "include Driver.Conceal"
          <//> sepWith hardline2 (sectionDoc <$> oadts)
    revealDoc =
      modDoc "Reveal" $
        "open Plaintext"
          </> "open Plaintext.Reveal"
          <//> go revealDefs
          <//> "include Driver.Reveal"
          <//> sepWith hardline2 (retractionDoc <$> oadts)
    modDoc name body =
      align $
        "module"
          <+> name
          <+> "= struct"
          </> indent body
          </> "end"

    sectionDoc OADTInfo {..} =
      let s = pretty $ toValidName section
          oadt = pretty $ toValidName oadtName
       in "let"
            <+> s <> "_"
            <+> "="
            <+> s
            </> "let"
            <+> s
            <+> "k x ="
            <+> parens
              ( "k, obliv_array_conceal_with"
                  <+> parens (s <> "_" <+> "k")
                  <+> "x"
              )
            </> "let"
            <+> s <> "_for"
            <+> "k party ="
            <+> parens
              ( "k, obliv_array_new_for"
                  <+> parens (oadt <+> "k")
                  <+> "party"
              )

    retractionDoc OADTInfo {..} =
      let r = pretty $ toValidName retraction
       in "let"
            <+> r <> "_"
            <+> "="
            <+> r
            </> "let"
            <+> r
            <+> parens "k, a"
            <+> "= obliv_array_reveal_with"
            <+> parens (r <> "_" <+> "k")
            <+> "a"

data OCamlDefKind = NonRecDef | RecDef | AndDef

-- | Translate all given OIL definitions into OCaml.
toOCamlDefs :: Options -> (forall a. Defs a) -> Doc
toOCamlDefs options defs =
  let defs' :: Defs a
      defs' = [def | def <- defs, isNothing $ isBuiltin def]
      edges = mkDepGraph defs'
      sccs = stronglyConnComp edges
      docs = foldMap go sccs
   in sepWith hardline2 docs
  where
    isBuiltin (name, FunDef {}) = isBuiltinExprName name
    isBuiltin (name, ADTDef {}) = isBuiltinTyName name
    go = runCuteM options . withExprNamePrefix . toOCamlSCCDef

-- | Translate a set of (mutually) recursively defined definitions.
toOCamlSCCDef :: SCC (NamedDef Text) -> CuteM [Doc]
toOCamlSCCDef (AcyclicSCC def) = one <$> toOCamlDef NonRecDef def
toOCamlSCCDef (CyclicSCC []) = return []
toOCamlSCCDef (CyclicSCC (def : defs)) = do
  doc <- toOCamlDef RecDef def
  docs <- mapM (toOCamlDef AndDef) defs
  return $ doc : docs

-- | Translate an OIL definition to OCaml definition.
--
-- The first argument indicates whether the definition is (mutually) recursively
-- defined.
toOCamlDef :: OCamlDefKind -> NamedDef Text -> CuteM Doc
toOCamlDef k (name, FunDef {..}) = do
  tyDoc <- toOCamlTy ty
  doc <- toOCamlLam True expr
  return $
    hang $
      kw
        <+> pretty (toValidName name)
          <> sep1 (colon <+> align (group tyDoc))
        <+> equals
          <> doc
  where
    kw = case k of
      NonRecDef -> "let"
      RecDef -> "let rec"
      AndDef -> "and"
toOCamlDef k (name, ADTDef {..}) = do
  ctorDocs <- mapM toOCamlCtor ctors
  return $
    hang $
      kw
        <+> pretty (toValidName name)
          <> sep1 (equals <+> sepWith (line <> pipe <> space) ctorDocs)
  where
    kw = case k of
      AndDef -> "and"
      _ -> "type"
    toOCamlCtor (ctor, paraTypes) = do
      let ctorDoc = pretty ctor
      -- In OCaml, parameter types of an ADT alternative are defined as if they
      -- form a tuple.
      docs <- forM paraTypes $ \t -> cuteSubDoc (TApp "*" []) t <$> toOCamlTy t
      return $
        if null docs
          then ctorDoc
          else
            hang $
              ctorDoc
                <+> "of"
                  <> sep1 (group $ sepWith (space <> "*" <> line) docs)

----------------------------------------------------------------
-- Naming related functions

withExprNamePrefix :: (MonadReader Options m) => m a -> m a
withExprNamePrefix = withNamePrefix "internal_x"

builtinExprTable :: [(Text, Text)]
builtinExprTable =
  [ ("True", "true"),
    ("False", "false"),
    ("()", "()"),
    (internalName "max", "max"),
    ("<=", "<="),
    ("==", "=="),
    ("+", "+"),
    ("-", "-"),
    ("*", "*"),
    ("/", "/"),
    ("not", "not"),
    ("&&", "&&"),
    ("||", "||")
  ]

builtinTyTable :: [(Text, Text)]
builtinTyTable =
  [ ("bool", "bool"),
    ("unit", "unit"),
    ("*", "*")
  ]

isBuiltinExprName :: Text -> Maybe Text
isBuiltinExprName x = lookup x builtinExprTable

isBuiltinTyName :: Text -> Maybe Text
isBuiltinTyName x = lookup x builtinTyTable

toValidComp :: Text -> Text
toValidComp = \case
  (T.stripPrefix oblivAccent -> Just x) -> "obliv_" <> toValidComp x
  (T.stripPrefix internalPrefix -> Just x) -> "internal_" <> toValidComp x
  x -> go x
  where
    go "*" = "int_mul"
    go "+" = "int_add"
    go "-" = "int_sub"
    go "/" = "int_div"
    go "==" = "int_eq"
    go "<=" = "int_le"
    go "not" = "bool_not"
    go "&&" = "bool_and"
    go "||" = "bool_or"
    go x | x == aName = "obliv_array"
    go (T.stripPrefix aName -> Just x) = "obliv_array_" <> x
    go x = x

toValidName :: Text -> Text
toValidName x = T.intercalate "_" $ toValidComp <$> T.splitOn instInfix x

isCtor :: Text -> Bool
isCtor "(,)" = True
isCtor x = maybe False (\(c, _) -> isUpper c) $ T.uncons x

----------------------------------------------------------------
-- Pretty printer helper functions

toOCamlApp :: Expr Text -> [Expr Text] -> CuteM Doc
toOCamlApp fn args = do
  fnDoc <- cuteSubAggDoc fn <$> toOCamlExpr fn
  toOCamlApp_ fnDoc args

toOCamlApp_ :: Doc -> [Expr Text] -> CuteM Doc
toOCamlApp_ fnDoc args = do
  docs <- forM args $ \arg -> cuteSubAggDoc arg <$> toOCamlExpr arg
  return $ cuteAppDoc fnDoc docs

toOCamlLam :: Bool -> Expr Text -> CuteM Doc
toOCamlLam isRoot e = do
  (binderDocs, bodyDoc) <- go e
  return $ cuteLamDoc_ ("fun" <> space) "->" isRoot binderDocs bodyDoc
  where
    go Lam {..} = do
      x <- toValidName <$> freshNameOrBinder binder
      (binderDocs, bodyDoc) <- go $ instantiateName x bnd
      return (pretty x : binderDocs, bodyDoc)
    go expr = ([],) <$> toOCamlExpr expr

toOCamlLet :: Doc -> Doc -> Doc -> Doc
toOCamlLet binderDoc rhsDoc bodyDoc =
  align $
    group
      ( hang
          ( "let"
              <+> (binderDoc <+> equals <> sep1 rhsDoc)
          )
          <> line
          <> "in"
      )
      </> bodyDoc

toOCamlTuple :: [Doc] -> Doc
toOCamlTuple = parens . align . sepWith (comma <> line)

toOCamlTyArgs :: [Ty] -> CuteM Doc
toOCamlTyArgs [] = return mempty
toOCamlTyArgs [arg] = cuteSubAggDoc arg <$> toOCamlTy arg
toOCamlTyArgs args = do
  argDocs <- mapM toOCamlTy args
  return $ hang $ group (toOCamlTuple argDocs <> line)

----------------------------------------------------------------
-- Dependency graph related functions

-- | Make the dependency graph.
--
-- This function returns the edges of the computed dependency graph. The return
-- type is in accordance with the container library APIs.
mkDepGraph :: (forall a. Defs a) -> [(NamedDef Text, DefKey, [DefKey])]
mkDepGraph defs =
  let depss = runFreshM $ mapM (go . snd) defs
   in zipWith (\def deps -> (def, toDefKey def, deps)) defs depss
  where
    go :: Def Name -> FreshM [DefKey]
    go FunDef {..} = do
      tDeps <- universeM ty <&> \es -> [TyKey x | TApp x _ <- es]
      eDeps <- universeM expr <&> \es -> [FunKey x | GV x <- es]
      return $ hashNub $ tDeps <> eDeps
    go ADTDef {..} = do
      let ts = foldMap snd ctors
      deps <- foldMapM universeM ts <&> \es -> [TyKey x | TApp x _ <- es]
      return $ hashNub deps

data DefKey = TyKey Text | FunKey Text
  deriving stock (Eq, Ord)

instance Hashable DefKey where
  hashWithSalt salt (TyKey s) = hashWithSalt salt s
  hashWithSalt salt (FunKey s) = hashWithSalt salt s

toDefKey :: NamedDef a -> DefKey
toDefKey (name, FunDef {}) = FunKey name
toDefKey (name, ADTDef {}) = TyKey name
