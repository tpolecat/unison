module Unison.Typechecker.Extractor where

import Control.Monad
import Control.Applicative
import Data.Foldable (toList)
import qualified Unison.Typechecker.Context as C



newtype NoteExtractor v loc a =
  NoteExtractor { run :: C.Note v loc -> Maybe a }

newtype PathExtractor v loc a =
  PathExtractor { runPath :: C.PathElement v loc -> Maybe a}

cause :: NoteExtractor v loc (C.Cause v loc)
cause = NoteExtractor $ pure . C.cause

path :: NoteExtractor v loc [C.PathElement v loc]
path = NoteExtractor $ pure . toList . C.path

mismatchedTerm :: NoteExtractor v loc (Maybe (C.Term v loc))
mismatchedTerm = NoteExtractor $ pure . C.innermostErrorTerm

-- subpath :: [Pattern] ->

-- App
-- = And
-- | Or
-- | IfCond
-- | Vector v
-- | Else v
-- | Match v
-- | Handle v

instance Functor (PathExtractor v loc) where
  fmap = liftM

instance Applicative (PathExtractor v loc) where
  (<*>) = ap
  pure = return

instance Monad (PathExtractor v loc) where
  fail _s = empty
  return a = PathExtractor (\_ -> Just a)
  PathExtractor r >>= f = PathExtractor go
    where
      go path = case r path of
        Nothing -> Nothing
        Just a -> runPath (f a) path

instance Alternative (PathExtractor v loc) where
  empty = mzero
  (<|>) = mplus

instance MonadPlus (PathExtractor v loc) where
  mzero = PathExtractor (\_ -> Nothing)
  mplus (PathExtractor f1) (PathExtractor f2) =
    PathExtractor (\note -> f1 note `mplus` f2 note)

instance Functor (NoteExtractor v loc) where
  fmap = liftM

instance Applicative (NoteExtractor v loc) where
  (<*>) = ap
  pure = return

instance Monad (NoteExtractor v loc) where
  fail _s = empty
  return a = NoteExtractor (\_ -> Just a)
  NoteExtractor r >>= f = NoteExtractor go
    where
      go note = case r note of
        Nothing -> Nothing
        Just a -> run (f a) note


instance Alternative (NoteExtractor v loc) where
  empty = mzero
  (<|>) = mplus

instance MonadPlus (NoteExtractor v loc) where
  mzero = NoteExtractor (\_ -> Nothing)
  mplus (NoteExtractor f1) (NoteExtractor f2) =
    NoteExtractor (\note -> f1 note `mplus` f2 note)
