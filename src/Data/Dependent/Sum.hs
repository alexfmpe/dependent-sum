{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Data.Dependent.Sum where

import Control.Applicative

import Data.Constraint.Extras
import Data.Type.Equality ((:~:) (..))

import Data.GADT.Show
import Data.GADT.Compare

import Data.Maybe (fromMaybe)
import Data.Some (Some(Some), foldSome)

import Text.Read
--import Control.Categorical.Bifunctor (Bifunctor)
import Data.Functor.Identity
import qualified Data.Functor.Product as Functor

-- | A basic dependent sum type where the first component is a tag
-- that specifies the type of the second. For example, think of a GADT
-- such as:
--
-- > data Tag a where
-- >    AString :: Tag String
-- >    AnInt   :: Tag Int
-- >    Rec     :: Tag (DSum Tag Identity)
--
-- Then we can write expressions where the RHS of @(':=>')@ has
-- different types depending on the @Tag@ constructor used. Here are
-- some expressions of type @DSum Tag 'Identity'@:
--
-- > AString :=> Identity "hello!"
-- > AnInt   :=> Identity 42
--
-- Often, the @f@ we choose has an 'Applicative' instance, and we can
-- use the helper function @('==>')@. The following expressions all
-- have the type @Applicative f => DSum Tag f@:
--
-- > AString ==> "hello!"
-- > AnInt   ==> 42
--
-- We can write functions that consume @DSum Tag f@ values by
-- matching, such as:
--
-- > toString :: DSum Tag Identity -> String
-- > toString (AString :=> Identity str) = str
-- > toString (AnInt   :=> Identity int) = show int
-- > toString (Rec     :=> Identity sum) = toString sum
--
-- The @(':=>')@ constructor and @('==>')@ helper are chosen to
-- resemble the @(key => value)@ construction for dictionary entries
-- in many dynamic languages. The @:=>@ and @==>@ operators have very
-- low precedence and bind to the right, making repeated use of these
-- operators behave as you'd expect:
--
-- > -- Parses as: Rec ==> (AnInt ==> (3 + 4))
-- > -- Has type: Applicative f => DSum Tag f
-- > Rec ==> AnInt ==> 3 + 4
--
-- The precedence of these operators is just above that of '$', so
-- @foo bar $ AString ==> "eep"@ is equivalent to @foo bar (AString
-- ==> "eep")@.
--
-- To use the 'Eq', 'Ord', 'Read', and 'Show' instances for @'DSum'
-- tag f@, you will need an 'ArgDict' instance for your tag type. Use
-- 'Data.Constraint.Extras.TH.deriveArgDict' from the
-- @constraints-extras@ package to generate this
-- instance.
data DSum tag f = forall a. !(tag a) :=> f a

infixr 1 :=>, ==>

-- | Convenience helper. Uses 'pure' to lift @a@ into @f a@.
(==>) :: Applicative f => tag a -> a -> DSum tag f
k ==> v = k :=> pure v

instance forall tag f. (GShow tag, Has' Show tag f) => Show (DSum tag f) where
    showsPrec p (tag :=> value) = showParen (p >= 10)
        ( gshowsPrec 0 tag
        . showString " :=> "
        . has' @Show @f tag (showsPrec 1 value)
        )

instance forall tag f. (GRead tag, Has' Read tag f) => Read (DSum tag f) where
    readsPrec p = readParen (p > 1) $ \s ->
        concat
            [ getGReadResult withTag $ \tag ->
                [ (tag :=> val, rest'')
                | (val, rest'') <- has' @Read @f tag (readsPrec 1 rest')
                ]
            | (withTag, rest) <- greadsPrec p s
            , let (con, rest') = splitAt 5 rest
            , con == " :=> "
            ]

instance forall tag f. (GEq tag, Has' Eq tag f) => Eq (DSum tag f) where
    (t1 :=> x1) == (t2 :=> x2)  = fromMaybe False $ do
        Refl <- geq t1 t2
        return $ has' @Eq @f t1 (x1 == x2)

instance forall tag f. (GCompare tag, Has' Eq tag f, Has' Ord tag f) => Ord (DSum tag f) where
    compare (t1 :=> x1) (t2 :=> x2)  = case gcompare t1 t2 of
        GLT -> LT
        GGT -> GT
        GEQ -> has' @Eq @f t1 $ has' @Ord @f t1 (x1 `compare` x2)

{-# DEPRECATED ShowTag "Instead of 'ShowTag tag f', use '(GShow tag, Has' Show tag f)'" #-}
type ShowTag tag f = (GShow tag, Has' Show tag f)

showTaggedPrec :: forall tag f a. (GShow tag, Has' Show tag f) => tag a -> Int -> f a -> ShowS
showTaggedPrec tag = has' @Show @f tag showsPrec

{-# DEPRECATED ReadTag "Instead of 'ReadTag tag f', use '(GRead tag, Has' Read tag f)'" #-}
type ReadTag tag f = (GRead tag, Has' Read tag f)

readTaggedPrec :: forall tag f a. (GRead tag, Has' Read tag f) => tag a -> Int -> ReadS (f a)
readTaggedPrec tag = has' @Read @f tag readsPrec

{-# DEPRECATED EqTag "Instead of 'EqTag tag f', use '(GEq tag, Has' Eq tag f)'" #-}
type EqTag tag f = (GEq tag, Has' Eq tag f)

eqTaggedPrec :: forall tag f a. (GEq tag, Has' Eq tag f) => tag a -> tag a -> f a -> f a -> Bool
eqTaggedPrec tag1 tag2 f1 f2 = case tag1 `geq` tag2 of
  Nothing -> False
  Just Refl -> has' @Eq @f tag1 $ f1 == f2

eqTagged :: forall tag f a. EqTag tag f => tag a -> tag a -> f a -> f a -> Bool
eqTagged k _ x0 x1 = has' @Eq @f k (x0 == x1)

{-# DEPRECATED OrdTag "Instead of 'OrdTag tag f', use '(GCompare tag, Has' Eq tag f, Has' Ord tag f)'" #-}
type OrdTag tag f = (GCompare tag, Has' Eq tag f, Has' Ord tag f)

compareTaggedPrec :: forall tag f a. (GCompare tag, Has' Eq tag f, Has' Ord tag f) => tag a -> tag a -> f a -> f a -> Ordering
compareTaggedPrec tag1 tag2 f1 f2 = case tag1 `gcompare` tag2 of
  GLT -> LT
  GEQ -> has' @Eq @f tag1 $ has' @Ord @f tag1 $ f1 `compare` f2
  GGT -> GT

compareTagged :: forall tag f a. OrdTag tag f => tag a -> tag a -> f a -> f a -> Ordering
compareTagged k _ x0 x1 = has' @Eq @f k $ has' @Ord @f k (compare x0 x1)

--someKey :: DSum k v -> Some k
--someKey (k :=> _) = Some k

--someValue :: DSum k v -> Some v
--someValue (_ :=> v) = Some v

fromKey :: (forall x. k x -> v x) -> Some k -> DSum k v
fromKey f = foldSome $ \k -> k :=> f k

fromValue :: (forall x. v x -> k x) -> Some v -> DSum k v
fromValue f = swapDSum . fromKey f

mapKey :: (forall x. k x -> k' x) -> DSum k v -> DSum k' v
mapKey f (k :=> v) = f k :=> v

mapValue :: (forall x. v x -> v' x) -> DSum k v -> DSum k v'
mapValue f (k :=> v) = k :=> f v

forKey :: Functor f => (forall x. k x -> f (k' x)) -> DSum k v -> f (DSum k' v)
forKey f (k :=> v) = (:=> v) <$> f k

forValue :: Functor f => (forall x. v x -> f (v' x)) -> DSum k v -> f (DSum k v')
forValue f (k :=> v) = (k :=>) <$> f v

dcurry :: (DSum k v -> a) -> (forall x. k x -> v x -> a)
dsum, duncurry :: (forall x. k x -> v x -> a) -> DSum k v -> a
dcurry f k v = f (k :=> v)

duncurry f (k :=> v) = f k v
dsum = duncurry

fromPair :: (k,v) -> DSum (Const k) (Const v)
fromPair (k,v) = Const k :=> Const v

toPair :: DSum (Const k) (Const v) -> (k,v)
toPair (Const k :=> Const v) = (k, v)

swapDSum :: DSum k v -> DSum v k
swapDSum (k :=> v) = v :=> k


type (~>) = NT
data NT f g where
  NT :: (forall x. f x -> g x) -> NT f g

class Product p a b | p -> a, p -> b where
  fst :: p -> a
  snd :: p -> b

instance Product (a,b) a b where
  fst = Prelude.fst
  snd = Prelude.snd

instance Product (Functor.Product a b x) (a x) (b x) where
  fst (Functor.Pair a b) = a
  snd (Functor.Pair a b) = b

instance Product (DSum a b) (Some a) (Some b) where
  fst (k :=> _) = Some k -- someKey
  snd (_ :=> v) = Some v -- someValue

{-
class Product p f where
  fst :: p a b -> f a
  snd :: p a b -> f b

instance Product (,) Identity where
  fst = Identity . Prelude.fst
  snd = Identity . Prelude.snd

instance Product DSum Some where
  fst (k :=> _) = Some k -- someKey
  snd (_ :=> v) = Some v --someValue

instance Product Functor.Product ()
-}
class PFunctor p s t where first  :: s a a' -> t (p a b) (p a' b)
class QFunctor p s t where second :: s b b' -> t (p a b) (p a b')
class Bifunctor p r s t where bimap :: r a a' -> s b b' -> t (p a b) (p a' b')

--instance (forall a b. Product (p a b) a b) => PFunctor p (->) (->) where
--  first f p =

--instance Bifunctor Functor.Product (->) (->) (->) where
instance Bifunctor (,) (->) (->) (->) where
  bimap f g (a,b) = (f a, g b)

instance Bifunctor Functor.Product (->) (->) (->) where -- (->) (->) (->) where

  bimap f g (Functor.Pair a b) = Functor.Pair (f a) (g b)

instance Bifunctor DSum (~>) (~>) (->) where
  bimap (NT fk) (NT fv) (k :=> v) = fk k :=> fv v


{-
instance PFunctor (,) (->) (->) where first  f (a,b) = (f a, b)
instance QFunctor (,) (->) (->) where second f (a,b) = (a, f b)

instance PFunctor DSum (~>) (->) where first  (NT f) (k :=> v) = f k :=> v -- mapKey
instance QFunctor DSum (~>) (->) where second (NT f) (k :=> v) = k :=> f v -- mapValue
-}
