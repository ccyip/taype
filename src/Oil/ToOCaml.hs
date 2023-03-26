{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
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
--     functions.
--
--   - ADT: OCaml constructor takes only one parameter, so we have to translate
--     multi-parameters to a single product type.
--
--   - (Mutual) recursion: we need to explicitly tell OCaml which functions are
--     (mutually) recursive.
--
-- We are being sloppy about naming at the moment, so there might be name
-- crashes. In particular, we use the prefixes \"obliv_\" and \"leaky_\" for the
-- oblivious and leaky things, while the users may use these prefixes too. This
-- can be easily solved by a more careful renaming scheme, but we choose to not
-- worry about it for simplicity and readability.
--
-- We reuse the boolean and product definitions in OCaml.
module Oil.ToOCaml (toOCaml) where

import Data.Char
import Data.Graph
  ( SCC (..),
    flattenSCC,
    graphFromEdges,
    reachable,
    stronglyConnComp,
  )
import Data.List (lookup)
import qualified Data.Text as T
import Oil.Syntax
import Prettyprinter.Util (reflow)
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
toOCamlExpr GV {..} | isCtor ref = cute $ toValidCtorName ref
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
  return $ cutePairDoc "" leftDoc rightDoc
toOCamlExpr
  App
    { fn = GV (isBuiltinExprName -> Just ref),
      ..
    } = toOCamlApp_ (pretty ref) args
toOCamlExpr App {fn = GV {..}, ..}
  | isCtor ref =
      let fnDoc = pretty (toValidCtorName ref)
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
toOCamlExpr
  Case
    { alts =
        [ CaseAlt {ctor = "False", binders = [], bnd = rBnd},
          CaseAlt {ctor = "True", binders = [], bnd = lBnd}
          ],
      ..
    } = do
    (_, left) <- unbindManyNamesOrBinders [] lBnd
    (_, right) <- unbindManyNamesOrBinders [] rBnd
    condDoc <- toOCamlExpr cond
    leftDoc <- toOCamlExpr left
    rightDoc <- toOCamlExpr right
    return $ cuteIteDoc "" condDoc leftDoc rightDoc
toOCamlExpr Case {alts = [CaseAlt {ctor = "(,)", ..}], ..} = do
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
toOCamlExpr Case {..} = do
  condDoc <- toOCamlExpr cond
  altDocs <- mapM goAltDoc alts
  return $
    align $
      "begin"
        <+> "match"
        <+> condDoc
        <+> "with"
          <> foldMap (\altDoc -> hardline <> pipe <+> altDoc) altDocs
          <> hardline
          <> "end"
  where
    goAltDoc CaseAlt {..} = do
      let ctor' = toValidCtorName ctor
      xs <- toValidName <<$>> mapM freshNameOrBinder binders
      bodyDoc <- toOCamlExpr $ instantiateName xs bnd
      return $
        hang $
          pretty ctor'
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
toOCamlTy :: Ty Text -> CuteM Doc
toOCamlTy TV {..} = cute name
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
  let tctor' = fromMaybe (toValidTyName tctor) $ isBuiltinTyName tctor
  argsDoc <- toOCamlTyArgs args
  return $ argsDoc <> pretty tctor'

----------------------------------------------------------------
-- Translate definitions

-- | Translate definitions into OCaml and open modules, with comments.
toOCaml :: Options -> Text -> [Text] -> (forall a. Defs a) -> Doc
toOCaml options header mods defs =
  headerDoc <> openDoc <> doc
  where
    headerDoc = "(*" <+> reflow header <+> "*)" <> hardline2
    openDoc = foldMap (\m -> "open" <+> pretty m <> hardline) mods <> hardline
    doc = runCuteM options $ withExprNamePrefix $ toOCamlDefs defs

data OCamlDefKind = NonRecDef | RecDef | AndDef

-- | Translate all given OIL definitions into OCaml.
toOCamlDefs :: (forall a. Defs a) -> CuteM Doc
toOCamlDefs defs = do
  let defs' = [def | def <- defs, isNothing $ isBuiltin def]
      edges = mkDepGraph defs'
      sccs = stronglyConnComp edges
  foldMapM ((foldMap end <$>) . toOCamlSCCDef) $ sortSCCs edges sccs
  where
    end doc = doc <> hardline2
    isBuiltin (name, FunDef {}) = isBuiltinExprName name
    isBuiltin (name, ADTDef {}) = isBuiltinTyName name

-- | Translate a set of (mutually) recursively defined definitions.
toOCamlSCCDef :: SCC (NamedDef Text) -> CuteM [Doc]
toOCamlSCCDef (AcyclicSCC def) = do
  (doc, docs) <- toOCamlDef NonRecDef def
  return $ doc : docs
toOCamlSCCDef (CyclicSCC []) = return []
toOCamlSCCDef (CyclicSCC (def : defs)) = do
  (fstDoc, fstDocs) <- toOCamlDef RecDef def
  res <- mapM (toOCamlDef AndDef) defs
  let (restDocs, restDocss) = unzip res
  return $ fstDoc : restDocs <> fstDocs <> concat restDocss

-- | Translate an OIL definition to OCaml definition.
--
-- The first argument indicates whether the definition is (mutually) recursively
-- defined.
--
-- This function returns the translated definition and extra definitions
-- associated with it.
toOCamlDef :: OCamlDefKind -> NamedDef Text -> CuteM (Doc, [Doc])
toOCamlDef k (name, FunDef {..}) = do
  xs <- withTyNamePrefix $ toValidTyVar <<$>> mapM freshNameOrBinder binders
  tyDoc <- toOCamlTy $ instantiateName xs tyBnd
  doc <- toOCamlLam True expr
  return
    ( hang $
        kw
          <+> pretty (toValidName name)
            <> sep1 (colon <+> align (group tyDoc))
          <+> equals
            <> doc,
      []
    )
  where
    kw = case k of
      NonRecDef -> "let"
      RecDef -> "let rec"
      AndDef -> "and"
toOCamlDef k (name, ADTDef {..}) = do
  xs <- withTyNamePrefix $ toValidTyVar <<$>> mapM freshNameOrBinder binders
  argsDoc <- toOCamlTyArgs $ TV <$> xs
  ctorDocs <- mapM (toOCamlCtor xs) ctors
  return
    ( hang $
        kw
          <+> argsDoc
            <> pretty (toValidTyName name)
            <> sep1 (equals <+> sepWith (line <> pipe <> space) ctorDocs),
      -- Because OCaml doesn't treat constructors as functions, we define a
      -- wrapper function for return or leaky if constructor.
      ctorWrapper (leakyAccent <> retractionPrefix) 1
        <> ctorWrapper promPrefix 1
        <> ctorWrapper lIfPrefix 3
    )
  where
    kw = case k of
      AndDef -> "and"
      _ -> "type"
    toOCamlCtor xs (ctor, paraBnds) = do
      let paraTypes = paraBnds <&> instantiateName xs
          ctorDoc = pretty $ capitalize $ toValidName ctor
      -- As if the parameter types are connected with product.
      docs <- forM paraTypes $ \t -> cuteSubDoc (TApp "*" []) t <$> toOCamlTy t
      return $
        if null docs
          then ctorDoc
          else
            hang $
              ctorDoc
                <+> "of"
                  <> sep1 (group $ sepWith (space <> "*" <> line) docs)
    ctorWrapper :: Text -> Int -> [Doc]
    ctorWrapper prefix arity =
      let xs = ("x" <>) . pretty <$> [1 .. arity]
       in [ hang $
              "let"
                <+> pretty (toValidName ctor)
                <+> hsep xs
                <+> equals
                  <> sep1
                    ( cuteAppDoc
                        (pretty $ toValidCtorName ctor)
                        ( if length xs < 2
                            then xs
                            else [group $ toOCamlTuple xs]
                        )
                    )
            | (ctor, _) <- ctors,
              T.isPrefixOf prefix ctor
          ]

----------------------------------------------------------------
-- Naming related functions

withExprNamePrefix :: MonadReader Options m => m a -> m a
withExprNamePrefix = withNamePrefix "internal_x"

withTyNamePrefix :: MonadReader Options m => m a -> m a
withTyNamePrefix = withNamePrefix "a"

builtinExprTable :: [(Text, Text)]
builtinExprTable =
  [ ("True", "true"),
    ("False", "false"),
    ("()", "()"),
    (internalName "max", "max"),
    (projName True, "fst"),
    (projName False, "snd"),
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

toValidName_ :: Bool -> Text -> Text
toValidName_ isTy = \case
  (T.stripPrefix promPrefix -> Just x) -> "leaky_prom_of_" <> toValidName_ True x
  (T.stripPrefix lIfPrefix -> Just x) -> "leaky_if_of_" <> toValidName_ True x
  (T.stripPrefix lCasePrefix -> Just x) -> "leaky_case_of_" <> toValidName_ True x
  (T.stripPrefix privPrefix -> Just x) -> "private_" <> toValidName_ isTy x
  (T.stripPrefix unsafePrefix -> Just x) -> "unsafe_" <> toValidName_ isTy x
  (T.stripPrefix oblivAccent -> Just x) -> "obliv_" <> toValidName_ isTy x
  (T.stripPrefix leakyAccent -> Just x) -> "leaky_" <> toValidName_ isTy x
  (T.stripPrefix internalPrefix -> Just x) -> "internal_" <> toValidName_ isTy x
  "" -> ""
  x ->
    let (x0, rest) = T.break (== '_') x
        (u, x') = T.span (== '_') rest
     in go isTy x0 <> u <> toValidName_ isTy x'
  where
    go True "*" = "prod"
    go False "*" = "int_mul"
    go True "+" = "sum"
    go False "+" = "int_add"
    go _ "-" = "int_sub"
    go _ "/" = "int_div"
    go _ "==" = "int_eq"
    go _ "<=" = "int_le"
    go _ "not" = "bool_not"
    go _ "&&" = "bool_and"
    go _ "||" = "bool_or"
    go _ "->" = "arrow"
    go _ "(,)" = "Pair"
    go _ x | x == aName = "obliv_array"
    go _ (T.stripPrefix aName -> Just x) = "obliv_array_" <> x
    go _ x = x

toValidTyName :: Text -> Text
toValidTyName = toValidName_ True

toValidName :: Text -> Text
toValidName = toValidName_ False

toValidCtorName :: Text -> Text
toValidCtorName = capitalize . toValidName

-- Similar to other naming transformation, we are being a bit sloppy and assume
-- no type variable starts with the leaky prefix.
toValidTyVar :: Text -> Text
toValidTyVar = \case
  (T.stripPrefix leakyAccent -> Just x) -> go ("leaky_" <> x)
  x -> go x
  where
    go = ("'" <>)

capitalize :: Text -> Text
capitalize x =
  case T.uncons x of
    Just (c, x') -> T.cons (toUpper c) x'
    _ -> x

isCtor :: Text -> Bool
isCtor = \case
  (T.stripPrefix promPrefix -> Just _) -> False
  (T.stripPrefix lIfPrefix -> Just _) -> False
  (T.stripPrefix lCasePrefix -> Just _) -> False
  (T.stripPrefix leakyAccent -> Just x) -> go x
  x -> go x
  where
    go "(,)" = True
    go x = maybe False (\(c, _) -> isUpper c) $ T.uncons x

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
  return $ cuteLamDoc_ ("fun" <> space) isRoot binderDocs bodyDoc
  where
    go Lam {..} = do
      x <- toValidName <$> freshNameOrBinder binder
      (binderDocs, bodyDoc) <- go $ instantiateName x bnd
      return (pretty x : binderDocs, bodyDoc)
    go expr = ([],) <$> toOCamlExpr expr

toOCamlLet :: Doc -> Doc -> Doc -> Doc
toOCamlLet binderDoc rhsDoc bodyDoc =
  align $
    "let"
      <+> hang (binderDoc <+> equals <> sep1 rhsDoc)
      <+> "in"
        <> hardline
        <> bodyDoc

toOCamlTuple :: [Doc] -> Doc
toOCamlTuple = parens . align . sepWith (comma <> line)

toOCamlTyArgs :: [Ty Text] -> CuteM Doc
toOCamlTyArgs [] = return mempty
toOCamlTyArgs [arg] = cuteSubAggDoc arg <$> toOCamlTy arg
toOCamlTyArgs args = do
  argDocs <- mapM toOCamlTy args
  return $ hang $ group (toOCamlTuple argDocs <> line)

----------------------------------------------------------------
-- Dependency graph related functions

-- | Sort the definition SCCs according to their dependencies and the user-given
-- order in the source code.
--
-- This process is totally unnecessary, as the SCCs are already in topological
-- order. It is also possibly quite inefficient. However, we still want to keep
-- the user-given order as much as possible for readability.
sortSCCs ::
  [(NamedDef Text, DefKey, [DefKey])] ->
  [SCC (NamedDef Text)] ->
  [SCC (NamedDef Text)]
sortSCCs edges sccs =
  sortBy sccCmp $ sortCyclic <$> sccs
  where
    (g, _, toVertex) = graphFromEdges edges
    table = mkTable (0 :: Int) edges
    mkTable _ [] = []
    mkTable i ((_, name, _) : edges') =
      let v = fromMaybe (-1) $ toVertex name
          r = reachable g v
       in (name, (i, v, r)) : mkTable (i + 1) edges'
    sortCyclic (CyclicSCC defs) = CyclicSCC $ sortOn defIndex defs
    sortCyclic scc = scc
    defIndex def = maybe (-1) (\(i, _, _) -> i) $ lookup (toDefKey def) table
    sccCmp scc scc' = cmp (getIdx scc) (getIdx scc')
    getIdx scc = fromMaybe (-1, -1, []) $ do
      def <- viaNonEmpty head $ flattenSCC scc
      lookup (toDefKey def) table
    cmp (i, v, r) (i', v', r') =
      if
          | v `elem` r' -> LT
          | v' `elem` r -> GT
          | otherwise -> compare i i'

-- | Make the dependency graph.
--
-- This function returns the edges of the computed dependency graph. The return
-- type is in accordance with the container library APIs.
mkDepGraph :: (forall a. Defs a) -> [(NamedDef Text, DefKey, [DefKey])]
mkDepGraph defs =
  let deps = runFreshM $ mapM (go . snd) defs
   in zipWith (\def dep -> (def, toDefKey def, dep)) defs deps
  where
    go :: Def Name -> FreshM [DefKey]
    go FunDef {..} = do
      (_, ty) <- unbindMany (length binders) tyBnd
      tDeps <- universeM ty <&> \es -> [TyKey x | TApp x _ <- es]
      eDeps <- universeM expr <&> \es -> [FunKey x | GV x <- es]
      return $ hashNub $ tDeps <> eDeps
    go ADTDef {..} = do
      xs <- freshes $ length binders
      let ts = foldMap (\(_, bnds) -> instantiateName xs <$> bnds) ctors
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
