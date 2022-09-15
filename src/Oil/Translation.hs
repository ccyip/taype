{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Translate taype to OIL.
--
-- We use naming convention to translate definition names and references to the
-- corresponding leaky types and leaky case analysis definitions, and to resolve
-- return and leaky if instances. This is more convenient than maintaining a
-- lookup table. The generated names contain characters that are illegal in the
-- taype identifiers to avoid name conflicts.
module Oil.Translation
  ( prelude,
    toOilDefs
  )
where

import Data.List (lookup)
import Oil.Syntax
import Relude.Extra.Bifunctor
import Taype.Common
import Taype.Environment (GCtx (..), TCtx (..), lookupGCtx)
import Taype.Name
import Taype.Prelude
import qualified Taype.Syntax as T

----------------------------------------------------------------
-- Naming

retName :: Text -> Text
retName x = "ret#" <> x

lIfName :: Text -> Text
lIfName x = oblivAccent <> "if#" <> x

lCaseName :: Text -> Text
lCaseName x = leakyAccent <> "case#" <> x

----------------------------------------------------------------
-- Environment for translation

data Env = Env
  { -- Taype global context
    gctx :: GCtx Name,
    -- Taype typing context
    tctx :: TCtx Name
  }

-- | The translation monad
type TslM = FreshT (Reader Env)

runTslM :: Env -> TslM a -> a
runTslM env m = runReader (runFreshT m) env

-- | Look up a taype definition in the global context.
lookupGDef :: MonadReader Env m => Text -> m (Maybe (T.Def Name))
lookupGDef x = lookupGCtx x <$> asks gctx

-- | Look up a taype type and its label in the context.
lookupTy :: MonadReader Env m => Name -> m (Maybe (T.Ty Name, Label))
lookupTy x = do
  TCtx tctx <- asks tctx
  return $ lookup x tctx

-- | Extend the taype typing context.
extendCtx ::
  MonadReader Env m => [(Name, T.Ty Name, Label)] -> m a -> m a
extendCtx xs = local go
  where
    go Env {tctx = TCtx tctx, ..} =
      Env {tctx = TCtx $ (xs <&> \(x, t, l) -> (x, (t, l))) <> tctx, ..}

-- | Extend the taype typing context with one entry.
extendCtx1 ::
  MonadReader Env m => Name -> T.Ty Name -> Label -> m a -> m a
extendCtx1 x t l = extendCtx [(x, t, l)]

----------------------------------------------------------------
-- Translation from taype to OIL

-- | Translate a taype expression with its label to the corresponding OIL
-- expression.
--
-- The taype expression is well-typed and in core taype ANF.
--
-- The resulting OIL expression should be typed by the corresponding translated
-- OIL type, under the translated typing context. The types and context are
-- translated according to 'toOilTy'.
--
-- The resulting OIL expression should also be behaviorally equivalent to the
-- taype expression.
toOilExpr :: Label -> T.Expr Name -> TslM (Expr Name)
toOilExpr _ _ = return $ GV "<unimplemented>"

-- | Translate a taype oblivious type to the OIL expression representing its
-- size.
--
-- The taype type is obliviously kinded and in core taype ANF.
--
-- The resulting OIL expression should be typed by 'sizeTy' under the translated
-- typing context, according to 'toOilTy'.
--
-- For a taype term typed by the given oblivious taype type, its translated OIL
-- term (according to 'toOilExpr') is an oblivious array of the size indicated
-- by the resulting OIL expression. In particular, if this taype term is closed,
-- the computed OIL expression is exactly the integer for the size of the
-- computed array.
toOilSize :: T.Ty Name -> TslM (Expr Name)
toOilSize _ = return $ GV "<unimplemented>"

-- | Translate a taype type with its label to the corresponding OIL type.
--
-- The taype type is well-kinded and in core taype ANF.
toOilTy :: Label -> T.Ty Name -> TslM (Ty b)
toOilTy SafeL = toOilTy_
toOilTy LeakyL = (toLeakyTy <$>) . toOilTy_

-- | Translate a taype type to the corresponding plain OIL type.
--
-- The taype type is well-kinded and in core taype ANF. The resulting OIL type
-- itself is not leaky, but function types may have leaky arguments.
--
-- If the taype type is obliviously kinded, then the result should be oblivious
-- array.
--
-- Two equivalent taype type should be translated to the same OIL type.
toOilTy_ :: T.Ty Name -> TslM (Ty b)
toOilTy_ T.TBool = return $ tGV "Bool"
toOilTy_ T.TInt = return TInt
toOilTy_ T.GV {..} = return $ tGV ref
toOilTy_ T.Prod {..} = do
  left' <- toOilTy_ left
  right' <- toOilTy_ right
  return $ "*" @@ [left', right']
toOilTy_ T.Pi {..} = do
  dom <- toOilTy (mustLabel label) ty
  (_, body) <- unbind1 bnd
  cod <- toOilTy_ body
  return Arrow {..}
-- Oblivious types, including type level computation, are translated into
-- oblivious array.
toOilTy_ _ = return OArray

-- | Translate an OIL type to its leaky counterpart.
--
-- Builtin types are translated to the leaky types in the 'prelude'.
-- User-defined ADTs are translated to the corresponding leaky types according
-- to our naming convention, i.e. the ADT names with the 'leakyAccent' prefix.
-- The actual definitions of the ADT leaky counterparts are generated when
-- translating ADT definitions.
toLeakyTy :: Ty a -> Ty a
toLeakyTy TInt = tGV $ leakyName "Int"
toLeakyTy OArray = tGV $ leakyName aName
toLeakyTy Arrow {..} = leakyName "->" @@ [dom, toLeakyTy cod]
toLeakyTy TApp {..} = TApp {tctor = leakyName tctor, args = toLeakyTy <$> args}
-- Local type variables do not appear in type translation.
toLeakyTy _ = oops "Local type variables appear"

-- | Translate taype definitions to the corresponding OIL definitions.
toOilDefs :: GCtx Name -> T.Defs Name -> Defs b a
toOilDefs gctx = foldMap go
  where
    go = secondF closedDef . runTslM Env {tctx = TCtx [], ..} . toOilDef

-- | Translate a taype definition to the corresponding OIL definition.
--
-- The ADT definition is translated to multiple OIL definitions, so this
-- function returns a list of OIL definitions.
toOilDef :: T.NamedDef Name -> TslM [NamedDef Name Name]
toOilDef (name, def) = case def of
  T.FunDef {..} -> do
    let l = mustLabel label
    ty' <- toOilTy l ty
    expr' <- toOilExpr l expr
    return $
      one
        ( name,
          FunDef
            { binders = [],
              tyBnd = abstract_ [] ty',
              expr = expr'
            }
        )
  T.OADTDef {..} -> do
    (x, body) <- unbind1 bnd
    body' <- extendCtx1 x ty SafeL $ toOilSize body
    ty' <- toOilTy SafeL ty
    return $
      one
        ( name,
          FunDef
            { binders = [],
              tyBnd = abstract_ [] $ Arrow ty' sizeTy,
              expr = Lam {bnd = abstract_ x body', ..}
            }
        )
  T.ADTDef {..} -> do
    return []
  _ -> oops "Translating constructor or builtin definitions"

----------------------------------------------------------------
-- Prelude

-- | The prelude with builtin types and functions
--
-- Because we do not type check these definitions, we need to be careful and
-- make sure all definitions are well-typed and in the right form. Specifically,
-- the alternatives in case analysis are in the canonical order. We do not need
-- to make sure constructors are in application form though, as this will be
-- handled later.
prelude :: Defs b a
prelude =
  [ -- Array
    adtDef_
      (l_ aName)
      []
      [ (ret_ aName, [OArray]),
        (lif_ aName, [OArray, "self", "self"])
      ],
    -- Boolean
    adtDef_
      "Bool"
      []
      [("False", []), ("True", [])],
    adtDef_
      (l_ "Bool")
      []
      [ (l_ "False", []),
        (l_ "True", []),
        (lif_ "Bool", [OArray, "self", "self"])
      ],
    funDef_
      (ret_ "Bool")
      []
      (ar_ ["Bool", l_ "Bool"])
      $ lam_ "b" $ ite_ "b" (l_ "True") (l_ "False"),
    funDef_
      (s_ "Bool")
      []
      (ar_ ["Bool", OArray])
      $ lam_ "b" $
        ite_ "b" (s_ "Int" @@ [ILit 1]) (s_ "Int" @@ [ILit 0]),
    funDef_
      (r_ "Bool")
      []
      (ar_ [OArray, l_ "Bool"])
      $ lam_ (o_ "b") $ lif_ "Bool" @@ [o_ "b", l_ "True", l_ "False"],
    funDef_
      (lcase_ "Bool")
      [l_ "r"]
      ( ar_
          [ ar_ [OArray, l_ "r", l_ "r", l_ "r"],
            l_ "Bool",
            l_ "r",
            l_ "r",
            l_ "r"
          ]
      )
      $ lams_ [lif_ "r", l_ "b", l_ "ff", l_ "ft"] $
        case_
          (l_ "b")
          [ (l_ "False", [], l_ "ff"),
            (l_ "True", [], l_ "ft"),
            ( lif_ "Bool",
              [o_ "b", l_ "b1", l_ "b2"],
              lif_ "r"
                @@ [ o_ "b",
                     "self" @@ [lif_ "r", l_ "b1", l_ "ff", l_ "ft"],
                     "self" @@ [lif_ "r", l_ "b2", l_ "ff", l_ "ft"]
                   ]
            )
          ],
    funDef_
      (l_ $ s_ "Bool")
      []
      (ar_ [l_ "Bool", l_ aName])
      $ lam_ (l_ "b") $
        case_
          (l_ "b")
          [ (l_ "False", [], ret_ aName @@ [s_ "Bool" @@ ["False"]]),
            (l_ "True", [], ret_ aName @@ [s_ "Bool" @@ ["True"]]),
            ( lif_ "Bool",
              [o_ "b", l_ "b1", l_ "b2"],
              lif_ aName
                @@ [o_ "b", "self" @@ [l_ "b1"], "self" @@ [l_ "b2"]]
            )
          ],
    -- Integer
    adtDef_
      (l_ "Int")
      []
      [ (r_ "Int", [OArray]),
        (ret_ "Int", [TInt]),
        (lif_ "Int", [OArray, "self", "self"])
      ],
    funDef_
      (l_ $ s_ "Int")
      []
      (ar_ [l_ "Int", l_ aName])
      $ lam_ (l_ "n") $
        case_
          (l_ "n")
          [ (r_ "Int", [o_ "n"], ret_ aName @@ [o_ "n"]),
            (ret_ "Int", ["n"], ret_ aName @@ [s_ "Int" @@ ["n"]]),
            ( lif_ "Int",
              [o_ "b", l_ "n1", l_ "n2"],
              lif_ aName
                @@ [o_ "b", "self" @@ [l_ "n1"], "self" @@ [l_ "n2"]]
            )
          ],
    lBopDef "+" "Int",
    lBopDef "-" "Int",
    lBopDef "<=" "Bool",
    lBopDef "==" "Bool",
    -- Product
    adtDef_
      "*"
      ["a", "b"]
      [("(,)", ["a", "b"])],
    adtDef_
      (l_ "*")
      [l_ "a", l_ "b"]
      [ (l_ "(,)", [l_ "a", l_ "b"]),
        ( lif_ "*",
          [ OArray,
            l_ "*" @@ [l_ "a", l_ "b"],
            l_ "*" @@ [l_ "a", l_ "b"]
          ]
        )
      ],
    funDef_
      (ret_ "*")
      ["a", l_ "a", "b", l_ "b"]
      ( ar_
          [ ar_ ["a", l_ "a"],
            ar_ ["b", l_ "b"],
            "*" @@ ["a", "b"],
            l_ "*" @@ [l_ "a", l_ "b"]
          ]
      )
      $ lams_ [ret_ "a", ret_ "b", "p"] $
        case_
          "p"
          [ ( "(,)",
              ["x", "y"],
              l_ "(,)" @@ [ret_ "a" @@ ["x"], ret_ "b" @@ ["y"]]
            )
          ],
    funDef_
      (lcase_ "*")
      [l_ "a", l_ "b", l_ "r"]
      ( ar_
          [ ar_ [OArray, l_ "r", l_ "r", l_ "r"],
            l_ "*" @@ [l_ "a", l_ "b"],
            ar_ [l_ "a", l_ "b", l_ "r"],
            l_ "r"
          ]
      )
      $ lams_ [lif_ "r", l_ "p", l_ "f"] $
        case_
          (l_ "p")
          [ (l_ "(,)", [l_ "x", l_ "y"], l_ "f" @@ [l_ "x", l_ "y"]),
            ( lif_ "*",
              [o_ "b", l_ "p1", l_ "p2"],
              lif_ "r"
                @@ [ o_ "b",
                     "self" @@ [lif_ "r", l_ "p1", l_ "f"],
                     "self" @@ [lif_ "r", l_ "p2", l_ "f"]
                   ]
            )
          ],
    -- Function type
    adtDef_
      (l_ "->")
      ["a", l_ "b"]
      [ (l_ "lam", [ar_ ["a", l_ "b"]]),
        ( lif_ "->",
          [ OArray,
            l_ "->" @@ ["a", l_ "b"],
            l_ "->" @@ ["a", l_ "b"]
          ]
        )
      ],
    funDef_
      (ret_ "->")
      ["a", "b", l_ "b"]
      (ar_ [ar_ ["b", l_ "b"], ar_ ["a", "b"], l_ "->" @@ ["a", l_ "b"]])
      $ lams_ [ret_ "b", "f"] $
        l_ "lam" @@ [lam_ "x" $ ret_ "b" @@ ["f" @@ ["x"]]],
    funDef_
      (l_ "ap")
      ["a", l_ "b"]
      ( ar_
          [ ar_ [OArray, l_ "b", l_ "b", l_ "b"],
            l_ "->" @@ ["a", l_ "b"],
            "a",
            l_ "b"
          ]
      )
      $ lams_ [lif_ "b", l_ "f", "x"] $
        case_
          (l_ "f")
          [ (l_ "lam", ["f"], "f" @@ ["x"]),
            ( lif_ "->",
              [o_ "b", l_ "f1", l_ "f2"],
              lif_ "b"
                @@ [ o_ "b",
                     "self" @@ [lif_ "b", l_ "f1", "x"],
                     "self" @@ [lif_ "b", l_ "f2", "x"]
                   ]
            )
          ],
    -- Tape
    funDef_
      (l_ "tape")
      []
      (ar_ [sizeTy, l_ aName, OArray])
      $ lams_ ["n", l_ "a"] $
        case_
          (l_ "a")
          [ (ret_ aName, [o_ "a"], o_ "a"),
            ( lif_ aName,
              [o_ "b", l_ "a1", l_ "a2"],
              V aMux
                @@ [ "n",
                     o_ "b",
                     "self" @@ ["n", l_ "a1"],
                     "self" @@ ["n", l_ "a2"]
                   ]
            )
          ],
    -- Oblivious injection
    funDef_
      (o_ "inl")
      []
      (ar_ [sizeTy, sizeTy, OArray, OArray])
      $ lams_ ["m", "n", o_ "a"] $
        V aConcat
          @@ [ s_ "Bool" @@ ["True"],
               ite_
                 ("<=" @@ ["n", "m"])
                 (o_ "a")
                 ( V aConcat
                     @@ [o_ "a", V aNew @@ ["-" @@ ["n", "m"]]]
                 )
             ],
    funDef_
      (o_ "inr")
      []
      (ar_ [sizeTy, sizeTy, OArray, OArray])
      $ lams_ ["m", "n", o_ "a"] $
        V aConcat
          @@ [ s_ "Bool" @@ ["False"],
               ite_
                 ("<=" @@ ["m", "n"])
                 (o_ "a")
                 ( V aConcat
                     @@ [o_ "a", V aNew @@ ["-" @@ ["m", "n"]]]
                 )
             ]
  ]

-- | Build a leaky definition for binary operator, e.g., '+'.
lBopDef :: Text -> Text -> NamedDef b a
lBopDef name cod =
  funDef_
    (l_ name)
    []
    (ar_ [l_ "Int", l_ "Int", l_ cod])
    $ lams_ [l_ "m", l_ "n"] $
      case_
        (l_ "m")
        [ ( r_ "Int",
            [o_ "m"],
            case_
              (l_ "n")
              [ ( r_ "Int",
                  [o_ "n"],
                  r_ cod
                    @@ [o_ name @@ [o_ "m", o_ "n"]]
                ),
                ( ret_ "Int",
                  ["n"],
                  r_ cod
                    @@ [o_ name @@ [o_ "m", s_ "Int" @@ ["n"]]]
                ),
                ( lif_ "Int",
                  [o_ "b", l_ "n1", l_ "n2"],
                  lif_ cod
                    @@ [ o_ "b",
                         "self" @@ [l_ "m", l_ "n1"],
                         "self" @@ [l_ "m", l_ "n2"]
                       ]
                )
              ]
          ),
          ( ret_ "Int",
            ["m"],
            case_
              (l_ "n")
              [ ( r_ "Int",
                  [o_ "n"],
                  r_ cod
                    @@ [o_ name @@ [s_ "Int" @@ ["m"], o_ "n"]]
                ),
                ( ret_ "Int",
                  ["n"],
                  ret_ cod
                    @@ [V name @@ ["m", "n"]]
                ),
                ( lif_ "Int",
                  [o_ "b", l_ "n1", l_ "n2"],
                  lif_ cod
                    @@ [ o_ "b",
                         "self" @@ [l_ "m", l_ "n1"],
                         "self" @@ [l_ "m", l_ "n2"]
                       ]
                )
              ]
          ),
          ( lif_ "Int",
            [o_ "b", l_ "m1", l_ "m2"],
            lif_ cod
              @@ [ o_ "b",
                   "self" @@ [l_ "m1", l_ "n"],
                   "self" @@ [l_ "m2", l_ "n"]
                 ]
          )
        ]

----------------------------------------------------------------
-- Smart constructors

l_ :: IsString a => Text -> a
l_ = fromString . toString . leakyName

o_ :: IsString a => Text -> a
o_ = fromString . toString . oblivName

s_ :: IsString a => Text -> a
s_ = fromString . toString . sectionName

r_ :: IsString a => Text -> a
r_ = fromString . toString . retractionName

lif_ :: IsString a => Text -> a
lif_ = fromString . toString . lIfName

ret_ :: IsString a => Text -> a
ret_ = fromString . toString . retName

lcase_ :: IsString a => Text -> a
lcase_ = fromString . toString . lCaseName
