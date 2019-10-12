{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Barbies.Internal.ConstraintsI
  ( ConstraintsI(..)
  , imapC
 , itraverseC
  , AllIF

  , CanDeriveConstraintsI
  , ibaddDictsDefault
  )

where

import Barbies.Generics.Constraints(GConstraints(..), GAll, TagSelf, Self, Other, X, Y)
import Barbies.Internal.Dicts(ClassF, Dict (..), requiringDict)
import Barbies.Internal.FunctorI(FunctorI (..))
import Barbies.Internal.TraversableI(TraversableI (..))

import Data.Functor.Product(Product(..))
import Data.Kind(Constraint)

import Data.Generics.GenericN


-- | Instances of this class provide means to talk about constraints,
--   both at compile-time, using 'AllI', and at run-time, in the form
--   of 'Dict', via ibaddDicts'.
--
--   A manual definition would look like this:
--
-- @
-- data T f a = A (f 'Int') (f 'String') | B (f 'Bool') (f 'Int')
--
-- instance 'ConstraintsI' T where
--   type 'AllI' c T = (c 'Int', c 'String', c 'Bool')
--
--   'ibaddDicts' t = case t of
--     A x y -> A ('Pair' 'Dict' x) ('Pair' 'Dict' y)
--     B z w -> B ('Pair' 'Dict' z) ('Pair' 'Dict' w)
-- @
--
-- Now, when we given a @T f@, if we need to use the 'Show' instance of
-- their fields, we can use:
--
-- @
-- ibaddDicts' :: AllI Show b => b f -> b ('Dict' 'Show' `Product` b)
-- @
--
-- There is a default implementation of 'ConstraintsI' for
-- 'Generic' types, so in practice one will simply do:
--
-- @
-- derive instance 'Generic' (T f a)
-- instance 'ConstraintsI' T
-- @
class FunctorI b => ConstraintsI (b :: (kl -> *) -> (kr -> *)) where
  -- | @'AllI' c b@ should contain a constraint @c a@ for each
  --   @a@ occurring under an @f@ in @b f@.
  --
  -- For requiring constraints of the form @c (f a)@, use 'AllIF'.
  type AllI (c :: k -> Constraint) b :: Constraint
  type AllI c b = GAll 1 c (GAllRepI b)

  iaddDicts
    :: forall c f x
    .  AllI c b
    => b f x
    -> b (Dict c `Product` f) x

  default iaddDicts
    :: forall c f x
    .  ( CanDeriveConstraintsI c b f x
       , AllI c b
       )
    => b f x -> b (Dict c `Product` f) x
  iaddDicts = ibaddDictsDefault


-- | Like 'imap' but a constraint is allowed to be required on
--   each element of @b@.
imapC :: forall c b f g x
      .  (AllI c b, ConstraintsI b)
      => (forall a. c a => f a -> g a)
      -> b f x
      -> b g x
imapC f bf
  = imap go (iaddDicts bf)
  where
    go :: forall a. (Dict c `Product` f) a -> g a
    go (d `Pair` fa) = requiringDict (f fa) d

-- | Like 'itraverse' but with a constraint on the elements of @b@.
itraverseC
  :: forall c b f g h x
  .  (TraversableI b, ConstraintsI b, AllI c b, Applicative g)
  => (forall a. c a => f a -> g (h a))
  -> b f x
  -> g (b h x)
itraverseC f b
  = itraverse (\(Pair (Dict :: Dict c a) x) -> f x) (iaddDicts b)

-- | Similar to 'AllI' but will put the functor argument @f@
--   between the constraint @c@ and the type @a@.
type AllIF c f b = AllI (ClassF c f) b


-- | @'CanDeriveConstraintsI' B f g x@ is in practice a predicate about @B@ only.
--   Intuitively, it says that the following holds, for any arbitrary @f@ and @x@:
--
--     * There is an instance of @'Generic' (B f x)@.
--
--     * @B f@ can contain fields of type @b f x@ as long as there exists a
--       @'ConstraintsI' b@ instance. In particular, recursive usages of @B f x@
--       are allowed.
type CanDeriveConstraintsI c b f x
  = ( GenericN (b f x)
    , GenericN (b (Dict c `Product` f) x)
    , AllI c b ~ GAll 1 c (GAllRepI b)
    , GConstraints 1 c f (GAllRepI b) (RepN (b f x)) (RepN (b (Dict c `Product` f) x))
    )

-- | The representation used for the generic computation of the @'AllI' c b@
--   constraints. Here 'X' and 'Y' are arbitrary constants since the actual
--   argument to @b@ is irrelevant.
type GAllRepI b = TagSelf 1 b (RepN (b X Y))

-- ===============================================================
--  Generic derivations
-- ===============================================================

-- | Default implementation of ibaddDicts' based on 'Generic'.
ibaddDictsDefault
  :: forall b c f x
  . ( CanDeriveConstraintsI c b f x
    , AllI c b
    )
  => b f x
  -> b (Dict c `Product` f) x
ibaddDictsDefault
  = toN . gaddDicts @1 @c @f @(GAllRepI b) . fromN
{-# INLINE ibaddDictsDefault #-}


-- ------------------------------------------------------------
-- Generic derivation: Special cases for ConstraintsI
-- -----------------------------------------------------------

type P = Param

instance
  ( ConstraintsI b
  , AllI c b
  ) => -- b' is b, maybe with 'Param' annotations
       GConstraints 1 c f (Rec (Self b' (P 1 X) (P 0 Y)) (b X Y))
                          (Rec (b' (P 1 f) (P 0 y)) (b f y))
                          (Rec (b' (P 1 (Dict c `Product` f)) (P 0 y))
                               (b       (Dict c `Product` f)       y))
  where
  gaddDicts
    = Rec . K1 . iaddDicts . unK1 . unRec
  {-# INLINE gaddDicts #-}


type instance GAll 1 c (Rec (Other b (P 1 X) (P 0 Y)) (b' X Y)) = AllI c b'

instance
  ( ConstraintsI b
  , AllI c b
  ) => GConstraints 1 c f (Rec (Other b' (P 1 X) (P 0 Y)) (b X Y))
                          (Rec (b' (P 1 f) (P 0 y)) (b f y))
                          (Rec (b' (P 1 (Dict c `Product` f)) (P 0 y))
                               (b       (Dict c `Product` f)       y))
  where
  gaddDicts
    = Rec . K1 . iaddDicts . unK1 . unRec
  {-# INLINE gaddDicts #-}
