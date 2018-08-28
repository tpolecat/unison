{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ViewPatterns #-}

module Unison.Type where

import qualified Data.Char as Char
import           Data.List
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           GHC.Generics
import           Prelude.Extras (Eq1(..),Show1(..))
import qualified Unison.ABT as ABT
import           Unison.Blank
import           Unison.Hashable (Hashable1)
import qualified Unison.Hashable as Hashable
import qualified Unison.Kind as K
import           Unison.Reference (Reference)
import qualified Unison.Reference as Reference
import           Unison.TypeVar (TypeVar)
import qualified Unison.TypeVar as TypeVar
import           Unison.Var (Var)
import qualified Unison.Var as Var

-- | Base functor for types in the Unison language
data F a
  = Ref Reference
  | Arrow a a
  | Ann a K.Kind
  | App a a
  | Effect a a -- effect type (either a single var or Effects list), value type
  | Effects Bool [a] -- can generalize?, effect list
  | Forall a
  deriving (Foldable,Functor,Generic,Generic1,Traversable)

instance Eq1 F where (==#) = (==)
instance Show1 F where showsPrec1 = showsPrec
instance Eq a => Eq (F a) where -- todo: derive automatically
  Ref r == Ref r2 = r == r2
  Arrow i o == Arrow i2 o2 = i == i2 && o == o2
  Ann a k == Ann a2 k2 = a == a2 && k == k2
  App f a == App f2 a2 = f == f2 && a == a2
  Effect es t == Effect es2 t2 = es == es2 && t == t2
  Effects can1 es1 == Effects can2 es2 = es1 == es2 && can1 == can2
  Forall a == Forall b = a == b
  _ == _ = False


-- | Types are represented as ABTs over the base functor F, with variables in `v`
type Type v = AnnotatedType v ()

-- | Like `Type v`, but with an annotation of type `a` at every level in the tree
type AnnotatedType v a = ABT.Term F v a

wrapV :: Ord v => AnnotatedType v a -> AnnotatedType (ABT.V v) a
wrapV = ABT.vmap ABT.Bound

freeVars :: AnnotatedType v a -> Set v
freeVars = ABT.freeVars

bindBuiltins :: Var v => [(v, Reference)] -> AnnotatedType v a -> AnnotatedType v a
bindBuiltins bs = ABT.substsInheritAnnotation [ (v, ref() r) | (v,r) <- bs ]

data Monotype v a = Monotype { getPolytype :: AnnotatedType v a } deriving Eq

instance (Var v) => Show (Monotype v a) where
  show = show . getPolytype

-- Smart constructor which checks if a `Type` has no `Forall` quantifiers.
monotype :: Var v => AnnotatedType v a -> Maybe (Monotype v a)
monotype t = Monotype <$> ABT.visit isMono t where
  isMono (Forall' _) = Just Nothing
  isMono _ = Nothing

arity :: AnnotatedType v a -> Int
arity (ForallNamed' _ body) = arity body
arity (Arrow' _ o) = 1 + arity o
arity _ = 0

-- some smart patterns
pattern Ref' r <- ABT.Tm' (Ref r)
pattern Arrow' i o <- ABT.Tm' (Arrow i o)
pattern Arrows' spine <- (unArrows -> Just spine)
pattern Ann' t k <- ABT.Tm' (Ann t k)
pattern App' f x <- ABT.Tm' (App f x)
pattern Apps' f args <- (unApps -> Just (f, args))
pattern Pure' t <- (unPure -> Just t)
pattern Effects' es <- ABT.Tm' (Effects _ es)
pattern EffectsCanGeneralize' can es <- ABT.Tm' (Effects can es)
-- Effect1' must match at least one effect
pattern Effect1' e t <- ABT.Tm' (Effect e t)
--pattern Effect' es t <- (unEffects1 -> Just (es, t))
pattern Effect'' es t <- (unEffect0 -> (es, t))
-- Effect0' may match zero effects
pattern Effect0' es t <- (unEffect0 -> (es, t))
pattern Forall' subst <- ABT.Tm' (Forall (ABT.Abs' subst))
pattern ForallsNamed' vs body <- (unForalls -> Just (vs, body))
pattern ForallNamed' v body <- ABT.Tm' (Forall (ABT.out -> ABT.Abs v body))
pattern Var' v <- ABT.Var' v
pattern Tuple' ts <- (unTuple -> Just ts)
pattern Existential' b v <- ABT.Var' (TypeVar.Existential b v)
pattern Universal' v <- ABT.Var' (TypeVar.Universal v)

unPure :: Ord v => AnnotatedType v a -> Maybe (AnnotatedType v a)
unPure (Effect'' [] t) = Just t
unPure t = Just t

unArrows :: AnnotatedType v a -> Maybe [AnnotatedType v a]
unArrows t =
  case go t of [_] -> Nothing; l -> Just l
  where
    go (Arrow' i o) = i : go o
    go o = [o]

unApps :: AnnotatedType v a -> Maybe (AnnotatedType v a, [AnnotatedType v a])
unApps t = case go t [] of [] -> Nothing; [_] -> Nothing; f:args -> Just (f,args)
  where
  go (App' i o) acc = go i (o:acc)
  go fn args = fn:args

unForalls :: AnnotatedType v a -> Maybe ([v], AnnotatedType v a)
unForalls t = go t []
  where go (ForallNamed' v body) vs = go body (v:vs)
        go _body [] = Nothing
        go body vs = Just(reverse vs, body)

unTuple :: Var v => AnnotatedType v a -> Maybe [AnnotatedType v a]
unTuple t = (case t of
    (Apps' (Ref' (Reference.Builtin "Pair")) [_,_]) -> id
    (Ref' (Reference.Builtin "()")) -> id
    _ -> const Nothing) $
    go t
    where go :: Var v => AnnotatedType v a -> Maybe [AnnotatedType v a]
          go (Apps' (Ref' (Reference.Builtin "Pair")) (t:t':[])) = (t:) <$> go t'
          go (Ref' (Reference.Builtin "()")) = Just []
          go _ = Nothing

unEffect0 :: Ord v => AnnotatedType v a -> ([AnnotatedType v a], AnnotatedType v a)
unEffect0 (Effect1' e a) = (snd $ flattenEffects False [e], a)
unEffect0 t = ([], t)

unEffects1 :: Ord v => AnnotatedType v a -> Maybe ([AnnotatedType v a], AnnotatedType v a)
unEffects1 (Effect1' (Effects' es) a) = Just (es, a)
unEffects1 _ = Nothing

matchExistential :: Eq v => v -> Type (TypeVar b v) -> Bool
matchExistential v (Existential' _ x) = x == v
matchExistential _ _ = False

matchUniversal :: Eq v => v -> Type (TypeVar b v) -> Bool
matchUniversal v (Universal' x) = x == v
matchUniversal _ _ = False

-- | True if the given type is a function, possibly quantified
isArrow :: Var v => Type v -> Bool
isArrow (ForallNamed' _ t) = isArrow t
isArrow (Arrow' _ _) = True
isArrow _ = False

-- some smart constructors

vector :: Ord v => a -> AnnotatedType v a
vector a = builtin a "Sequence"

--vectorOf :: Ord v => a -> AnnotatedType v a -> Type v
--vectorOf a t = vector `app` t

ref :: Ord v => a -> Reference -> AnnotatedType v a
ref a = ABT.tm' a . Ref

builtin :: Ord v => a -> Text -> AnnotatedType v a
builtin a = ref a . Reference.Builtin

int64 :: Ord v => a -> AnnotatedType v a
int64 a = builtin a "Int64"

uint64 :: Ord v => a -> AnnotatedType v a
uint64 a = builtin a "UInt64"

float :: Ord v => a -> AnnotatedType v a
float a = builtin a "Float"

boolean :: Ord v => a -> AnnotatedType v a
boolean a = builtin a "Boolean"

text :: Ord v => a -> AnnotatedType v a
text a = builtin a "Text"

stream :: Ord v => a -> AnnotatedType v a
stream a = builtin a "Stream"

app :: Ord v => a -> AnnotatedType v a -> AnnotatedType v a -> AnnotatedType v a
app a f arg = ABT.tm' a (App f arg)

-- `f x y z` means `((f x) y) z` and the annotation paired with `y` is the one
-- meant for `app (f x) y`
apps :: Ord v => AnnotatedType v a -> [(a, AnnotatedType v a)] -> AnnotatedType v a
apps f params = foldl' go f params where
  go f (a,t) = app a f t

arrow :: Ord v => a -> AnnotatedType v a -> AnnotatedType v a -> AnnotatedType v a
arrow a i o = ABT.tm' a (Arrow i o)

ann :: Ord v => a -> AnnotatedType v a -> K.Kind -> AnnotatedType v a
ann a e t = ABT.tm' a (Ann e t)

forall :: Ord v => a -> v -> AnnotatedType v a -> AnnotatedType v a
forall a v body = ABT.tm' a (Forall (ABT.abs' a v body))

iff :: Var v => Type v
iff = forall () aa $ arrows (f <$> [boolean(), a, a]) a
  where aa = ABT.v' "a"
        a = var () aa
        f x = ((), x)

iff' :: Var v => a -> AnnotatedType v a
iff' loc = forall loc aa $ arrows (f <$> [boolean loc, a, a]) a
  where aa = ABT.v' "a"
        a = var loc aa
        f x = (loc, x)

iff2 :: Var v => a -> AnnotatedType v a
iff2 loc = forall loc aa $ arrows (f <$> [a, a]) a
  where aa = ABT.v' "a"
        a = var loc aa
        f x = (loc, x)

andor :: Ord v => Type v
andor = arrows (f <$> [boolean(), boolean()]) $ boolean()
  where f x = ((), x)

andor' :: Ord v => a -> AnnotatedType v a
andor' a = arrows (f <$> [boolean a, boolean a]) $ boolean a
  where f x = (a, x)

var :: Ord v => a -> v -> AnnotatedType v a
var = ABT.annotatedVar

existential :: Ord v => Blank loc -> v -> Type (TypeVar (Blank loc) v)
existential blank v = ABT.var (TypeVar.Existential blank v)

universal :: Ord v => v -> Type (TypeVar b v)
universal v = ABT.var (TypeVar.Universal v)

existentialp :: Ord v => a -> v -> AnnotatedType (TypeVar (Blank x) v) a
existentialp a v = existential' a Blank v

existential' :: Ord v => a -> Blank x -> v -> AnnotatedType (TypeVar (Blank x) v) a
existential' a blank v = ABT.annotatedVar a (TypeVar.Existential blank v)

universal' :: Ord v => a -> v -> AnnotatedType (TypeVar b v) a
universal' a v = ABT.annotatedVar a (TypeVar.Universal v)

v' :: Var v => Text -> Type v
v' s = ABT.var (ABT.v' s)

-- Like `v'`, but creates an annotated variable given an annotation
av' :: Var v => a -> Text -> AnnotatedType v a
av' a s = ABT.annotatedVar a (ABT.v' s)

forall' :: Var v => a -> [Text] -> AnnotatedType v a -> AnnotatedType v a
forall' a vs body = foldr (forall a) body (Var.named <$> vs)

foralls :: Var v => a -> [v] -> AnnotatedType v a -> AnnotatedType v a
foralls a vs body = foldr (forall a) body vs

-- Note: `a -> b -> c` parses as `a -> (b -> c)`
-- the annotation associated with `b` will be the annotation for the `b -> c`
-- node
arrows :: Ord v => [(a, AnnotatedType v a)] -> AnnotatedType v a -> AnnotatedType v a
arrows ts result = foldr go result ts where
  go (a,t) result = arrow a t result

-- The types of effectful computations
effect :: Ord v => a -> Bool -> [AnnotatedType v a] -> AnnotatedType v a -> AnnotatedType v a
effect a canGeneralize es (Effect1' f t) =
  let (canEs, es') = flattenEffects canGeneralize es
      (canFs, fs') = flattenEffects canEs [f]
      effects = es' ++ fs'
  in ABT.tm' a (Effect (ABT.tm' a (Effects canFs effects)) t)
effect a can es t = ABT.tm' a (Effect (ABT.tm' a (Effects can es)) t)

effects :: Ord v => a -> Bool -> [AnnotatedType v a] -> AnnotatedType v a
effects a canGeneralize es =
  let (canGeneralize', es') = flattenEffects canGeneralize es
  in ABT.tm' a (Effects canGeneralize' es')

effect1 :: Ord v => a -> AnnotatedType v a -> AnnotatedType v a -> AnnotatedType v a
effect1 a e (Effect1' f t) =
  let (canGeneralizeEs, e') = flattenEffects False [e]
      (canGeneralizeFs, f') = flattenEffects False [f]
      canGeneralize = canGeneralizeEs || canGeneralizeFs
      effects = e' ++ f'
  in ABT.tm' a (Effect (ABT.tm' a (Effects canGeneralize effects)) t)
effect1 a es t = ABT.tm' a (Effect es t)

flattenEffects :: Bool -> [AnnotatedType v a] -> (Bool, [AnnotatedType v a])
flattenEffects can [] = (can, [])
flattenEffects can (h:t) = case h of
  EffectsCanGeneralize' can' es -> flattenEffects (can || can') (es ++ t)
  _ -> case flattenEffects can t of (b, ts) -> (b, h : ts)

-- The types of first-class effect values
-- which get deconstructed in effect handlers.
effectV :: Ord v => a -> (a, AnnotatedType v a) -> (a, AnnotatedType v a) -> AnnotatedType v a
effectV builtinA e t = apps (builtin builtinA "Effect") [e, t]

-- Strips effects from a type. E.g. `{e} a` becomes `a`.
--stripEffect :: Ord v => AnnotatedType v a -> ([AnnotatedType v a], AnnotatedType v a)
--stripEffect (Effect' e t) = case stripEffect t of (ei, t) -> (e ++ ei, t)
--stripEffect t = ([], t)

-- The type of the flipped function application operator:
-- `(a -> (a -> b) -> b)`
flipApply :: Var v => Type v -> Type v
flipApply t = forall() b $ arrow() (arrow() t (var() b)) (var() b)
  where b = ABT.fresh t (ABT.v' "b")

-- | Bind all free variables with an outer `forall`.
generalize :: Ord v => AnnotatedType v a -> AnnotatedType v a
generalize t = foldr (forall (ABT.annotation t)) t $ Set.toList (ABT.freeVars t)

-- map : (a -> b) -> List a -> List b
-- map : (a -> {e} b) -> List a -> {e} (List b)
--
-- map : (a ->{e1} b) ->{e2} List a ->{e1,} (List b)
generalizeEffects :: Var v => AnnotatedType v a -> AnnotatedType v a
generalizeEffects t = let
  at = ABT.annotation t
  e = ABT.fresh t (Var.named "e")
  ev t = effect1 at (var at e) t
  -- if `arg` is `{} blah` leave it alone or need some way of telling typechecker
  -- to leave it alone
  go t@(Arrow' f arg) = arrow (ABT.annotation t) f (ev arg)
  go _t@(Ann' _a _) = error "todo"
  go _ = error "todo"
  in forall (ABT.annotation t) e (go t)

-- | Bind all free variables that start with a lowercase letter with an outer `forall`.
generalizeLowercase :: Var v => AnnotatedType v a -> AnnotatedType v a
generalizeLowercase t = foldr (forall (ABT.annotation t)) t vars
  where vars = [ v | v <- Set.toList (ABT.freeVars t), isLow v]
        isLow v = all Char.isLower . take 1 . Text.unpack . Var.name $ v

instance Hashable1 F where
  hash1 hashCycle hash e =
    let
      (tag, hashed) = (Hashable.Tag, Hashable.Hashed)
      -- Note: start each layer with leading `0` byte, to avoid collisions with
      -- terms, which start each layer with leading `1`. See `Hashable1 Term.F`
    in Hashable.accumulate $ tag 0 : case e of
      Ref r -> [tag 0, Hashable.accumulateToken r]
      Arrow a b -> [tag 1, hashed (hash a), hashed (hash b) ]
      App a b -> [tag 2, hashed (hash a), hashed (hash b) ]
      Ann a k -> [tag 3, hashed (hash a), Hashable.accumulateToken k ]
      -- Example:
      --   a) {Remote, Abort} (() -> {Remote} ()) should hash the same as
      --   b) {Abort, Remote} (() -> {Remote} ()) but should hash differently from
      --   c) {Remote, Abort} (() -> {Abort} ())
      Effects b es -> let
        (hs, _) = hashCycle es
        in [tag 4, Hashable.accumulateToken b] ++ map hashed hs
      Effect e t -> [tag 5, hashed (hash e), hashed (hash t)]
      Forall a -> [tag 6, hashed (hash a)]

instance Show a => Show (F a) where
  showsPrec p fa = go p fa where
    go _ (Ref r) = showsPrec 0 r
    go p (Arrow i o) =
      showParen (p > 0) $ showsPrec (p+1) i <> s" -> " <> showsPrec p o
    go p (Ann t k) =
      showParen (p > 1) $ showsPrec 0 t <> s":" <> showsPrec 0 k
    go p (App f x) =
      showParen (p > 9) $ showsPrec 9 f <> s" " <> showsPrec 10 x
    go p (Effects True es) = showParen (p > 0) $
      s"{" <> showsPrec 0 es <> s"}"
    go p (Effects False es) = showParen (p > 0) $
      s"{|" <> showsPrec 0 es <> s"|}"
    go p (Effect e t) = showParen (p > 0) $
     showsPrec 0 e <> s" " <> showsPrec p t
    go p (Forall body) = case p of
      0 -> showsPrec p body
      _ -> showParen True $ s"∀ " <> showsPrec 0 body
    (<>) = (.)
    s = showString
