module Unison.Term where

import Dict
import Dict (Dict)
import Json
import Set
import Set (Set)
import Graphics.Element as Element
import Graphics.Input (Handle, hoverable)
import Text(..)
import Unison.Styles as Styles
import Unison.Hash (Hash)
import Unison.Hash as H
import Unison.Jsonify as J
import Unison.Jsonify (Jsonify)
import Unison.Metadata as Metadata
import Unison.Metadata (Metadata)
import Unison.Parser as P
import Unison.Parser (Parser)
import Unison.Var (I)
import Unison.Var as V
import Unison.Type as T

data Literal
  = Number Float
  | String String
  | Vector [Term]

data Term
  = Var I
  | Lit Literal
  | Con Hash
  | Ref Hash
  | App Term Term
  | Ann Term T.Type
  | Lam I Term

data E
  = Fn -- ^ Points at function in a function application
  | Arg -- ^ Points at the argument of a function application
  | Body -- ^ Points at the body of a lambda

type Path = [E]

render : Term -- term to render
      -> { handle         : Handle (Maybe (k, Path))
         , key            : k
         , highlighted    : Set Path
         , availableWidth : Int
         , metadata       : Dict k Metadata }
      -> Element
render expr env =
  let
    msg path b = if b then Just (env.key, reverse path) else Nothing
    -- basically, try calling with breakDepth of zero, then 1, then 2
    -- until it fits in the remaining width
    go : Int -> Int -> Int -> Path -> Term -> Element
    go ambientPrec breakDepth remWidth path cur = case cur of
      Var n -> style Styles.code (toText (show n))
            |> leftAligned
            |> hoverable env.handle (msg path)
      _ -> todo
  in todo

-- break (f x y z) == (f, [x, y, z])
break : Term -> (Term, [Term])
break expr = todo

-- try laying out the term all on one line, then progressively break
-- need a Map Hash Metadata
--

todo : a
todo = todo

parseLiteral : Parser Literal
parseLiteral = P.union' <| \t ->
  if | t == "Number" -> P.map Number P.number
     | t == "String" -> P.map String P.string
     | t == "Vector" -> P.map Vector (P.array parseTerm)

parseTerm : Parser Term
parseTerm = P.union' <| \t ->
  if | t == "Var" -> P.map Var V.parse
     | t == "Lit" -> P.map Lit parseLiteral
     | t == "Con" -> P.map Con H.parse
     | t == "Ref" -> P.map Ref H.parse
     | t == "App" -> P.lift2 App parseTerm parseTerm
     | t == "Ann" -> P.lift2 Ann parseTerm T.parseType
     | t == "Lam" -> P.lift2 Lam V.parse parseTerm

jsonifyLiteral l = case l of
  Number n -> J.tag' "Number" J.number n
  String s -> J.tag' "String" J.string s
  Vector es -> J.tag' "Vector" (J.array jsonifyTerm) es

jsonifyTerm : Jsonify Term
jsonifyTerm e = case e of
  Var v -> J.tag' "Var" V.jsonify v
  Lit l -> J.tag' "Lit" jsonifyLiteral l
  Con h -> J.tag' "Con" H.jsonify h
  Ref h -> J.tag' "Ref" H.jsonify h
  App f x -> J.tag' "App" (J.array jsonifyTerm) [f, x]
  Ann e t -> J.tag' "Ann" (J.tuple2 jsonifyTerm T.jsonifyType) (e, t)
  Lam n body -> J.tag' "Lam" (J.tuple2 V.jsonify jsonifyTerm) (n, body)

jsonifyE : Jsonify E
jsonifyE e = case e of
  Fn -> J.string "Fn"
  Arg -> J.string "Arg"
  Body -> J.string "Body"

jsonifyPath : Jsonify Path
jsonifyPath = J.array jsonifyE