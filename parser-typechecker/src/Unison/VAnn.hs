{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Unison.VAnn where

import qualified Unison.Lexer as L
-- import qualified Unison.Parser as P

-- note: whoops; we don't have these v's until typechecking
data Special v
  = And
  | Or
  | IfCond
  | Vector v
  | Else v
  | Match v
  | Handle v
  deriving (Eq, Ord, Show, Functor)

data VAnn v
  = Intrinsic
  -- Codebase { hash :: Hash, path :: _}
  | Text { start :: L.Pos, end :: L.Pos, special :: Maybe (Special v) }
  deriving (Eq, Ord, Show, Functor)
