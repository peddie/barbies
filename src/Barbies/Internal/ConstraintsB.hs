{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Barbies.Internal.ConstraintsB
  ( ConstraintsB(..)
  , bmapC
  , btraverseC
  , AllBF
  , bdicts
  , bpureC
  , bmempty

  , CanDeriveConstraintsB
  , gbaddDictsDefault
  , GAllRepB
  )

where

import Barbies.Generics.Constraints(GConstraints(..), GAll, TagSelf, Self, Other, X)
import Barbies.Internal.ApplicativeB(ApplicativeB(..))
import Barbies.Internal.Dicts(ClassF, Dict (..), requiringDict)
import Barbies.Internal.FunctorB(FunctorB (..))
import Barbies.Internal.TraversableB(TraversableB (..))

import Data.Functor.Compose (Compose (..))
import Data.Functor.Const   (Const (..))
import Data.Functor.Product (Product (..))
import Data.Functor.Sum     (Sum (..))
import Data.Kind            (Constraint)
import Data.Proxy           (Proxy (..))

import Data.Generics.GenericN


-- | Instances of this class provide means to talk about constraints,
--   both at compile-time, using 'AllB', and at run-time, in the form
--   of 'Dict', via 'baddDicts'.
--
--   A manual definition would look like this:
--
-- @
-- data T f = A (f 'Int') (f 'String') | B (f 'Bool') (f 'Int')
--
-- instance 'ConstraintsB' T where
--   type 'AllB' c T = (c 'Int', c 'String', c 'Bool')
--
--   'baddDicts' t = case t of
--     A x y -> A ('Pair' 'Dict' x) ('Pair' 'Dict' y)
--     B z w -> B ('Pair' 'Dict' z) ('Pair' 'Dict' w)
-- @
--
-- Now, when we given a @T f@, if we need to use the 'Show' instance of
-- their fields, we can use:
--
-- @
-- 'baddDicts' :: AllB Show b => b f -> b ('Dict' 'Show' `Product` b)
-- @
--
-- There is a default implementation of 'ConstraintsB' for
-- 'Generic' types, so in practice one will simply do:
--
-- @
-- derive instance 'Generic' (T f)
-- instance 'ConstraintsB' T
-- @
class FunctorB b => ConstraintsB (b :: (k -> *) -> *) where
  -- | @'AllB' c b@ should contain a constraint @c a@ for each
  --   @a@ occurring under an @f@ in @b f@. E.g.:
  --
  -- @
  -- 'AllB' 'Show' Person ~ ('Show' 'String', 'Show' 'Int')
  -- @
  --
  -- For requiring constraints of the form @c (f a)@, use 'AllBF'.
  type AllB (c :: k -> Constraint) b :: Constraint
  type AllB c b = GAll 0 c (GAllRepB b)

  baddDicts
    :: forall c f
    .  AllB c b
    => b f
    -> b (Dict c `Product` f)

  default baddDicts
    :: forall c f
    .  ( CanDeriveConstraintsB c b f
       , AllB c b
       )
    => b f -> b (Dict c `Product` f)
  baddDicts = gbaddDictsDefault


-- | Like 'bmap' but a constraint is allowed to be required on
--   each element of @b@
--
-- E.g. If all fields of 'b' are 'Show'able then you
-- could store each shown value in it's slot using 'Const':
--
-- > showFields :: (AllB Show b, ConstraintsB b) => b Identity -> b (Const String)
-- > showFields = bmapC @Show showField
-- >   where
-- >     showField :: forall a. Show a => Identity a -> Const String a
-- >     showField (Identity a) = Const (show a)
bmapC :: forall c b f g
      .  (AllB c b, ConstraintsB b)
      => (forall a. c a => f a -> g a)
      -> b f
      -> b g
bmapC f bf
  = bmap go (baddDicts bf)
  where
    go :: forall a. (Dict c `Product` f) a -> g a
    go (d `Pair` fa) = requiringDict (f fa) d

-- | Like 'btraverse' but with a constraint on the elements of @b@.
btraverseC
  :: forall c b f g h
  .  (TraversableB b, ConstraintsB b, AllB c b, Applicative g)
  => (forall a. c a => f a -> g (h a))
  -> b f
  -> g (b h)
btraverseC f b
  = btraverse (\(Pair (Dict :: Dict c a) x) -> f x) (baddDicts b)

-- | Similar to 'AllB' but will put the functor argument @f@
--   between the constraint @c@ and the type @a@. For example:
--
--   @
--   'AllB'  'Show'   Person ~ ('Show'    'String',  'Show'    'Int')
--   'AllBF' 'Show' f Person ~ ('Show' (f 'String'), 'Show' (f 'Int'))
--   @
type AllBF c f b = AllB (ClassF c f) b


-- | Similar to 'baddDicts' but can produce the instance dictionaries
--   "out of the blue".
bdicts
  :: forall c b
  . (ConstraintsB b, ApplicativeB b,  AllB c b)
  => b (Dict c)
bdicts
  = bmap (\(Pair c _) -> c) $ baddDicts $ bpure Proxy


-- | Like 'bpure' but a constraint is allowed to be required on
--   each element of @b@.
bpureC
  :: forall c f b
  .  ( AllB c b
     , ConstraintsB b
     , ApplicativeB b
     )
  => (forall a . c a => f a)
  -> b f
bpureC fa
  = bmap (requiringDict @c fa) bdicts

-- | Builds a @b f@, by applying 'mempty' on every field of @b@.
bmempty
  :: forall f b
  .  ( AllBF Monoid f b
     , ConstraintsB b
     , ApplicativeB b
     )
  => b f
bmempty
  = bpureC @(ClassF Monoid f) mempty


-- | @'CanDeriveConstraintsB' B f g@ is in practice a predicate about @B@ only.
--   Intuitively, it says that the following holds, for any arbitrary @f@:
--
--     * There is an instance of @'Generic' (B f)@.
--
--     * @B f@ can contain fields of type @b f@ as long as there exists a
--       @'ConstraintsB' b@ instance. In particular, recursive usages of @B f@
--       are allowed.
type CanDeriveConstraintsB c b f
  = ( GenericN (b f)
    , GenericN (b (Dict c `Product` f))
    , AllB c b ~ GAll 0 c (GAllRepB b)
    , GConstraints 0 c f (GAllRepB b) (RepN (b f)) (RepN (b (Dict c `Product` f)))
    )

-- | The representation used for the generic computation of the @'AllB' c b@
--   constraints. Here 'X' is an arbitrary constant since the actual
--   argument to @b@ is irrelevant.
type GAllRepB b = TagSelf 0 b (RepN (b X))


-- ===============================================================
--  Generic derivations
-- ===============================================================

-- | Default implementation of 'baddDicts' based on 'Generic'.
gbaddDictsDefault
  :: forall b c f
  . ( CanDeriveConstraintsB c b f
    , AllB c b
    )
  => b f
  -> b (Dict c `Product` f)
gbaddDictsDefault
  = toN . gaddDicts @0 @c @f @(GAllRepB b) . fromN
{-# INLINE gbaddDictsDefault #-}


-- ------------------------------------------------------------
-- Generic derivation: Special cases for ConstraintsB
-- -----------------------------------------------------------

type P = Param


instance
  ( ConstraintsB b
  , AllB c b
  ) => -- b' is b, maybe with 'Param' annotations
       GConstraints 0 c f (Rec (Self b' (P 0 X)) (b X))
                          (Rec (b' (P 0 f)) (b f))
                          (Rec (b' (P 0 (Dict c `Product` f)))
                               (b       (Dict c `Product` f)))
  where
  gaddDicts
    = Rec . K1 . baddDicts . unK1 . unRec
  {-# INLINE gaddDicts #-}


type instance GAll 0 c (Rec (Other b (P 0 X)) (b' X)) = AllB c b'

instance
  ( ConstraintsB b
  , AllB c b
  ) => GConstraints 0 c f (Rec (Other b' (P 0 X)) (b X))
                          (Rec (b' (P 0 f)) (b f))
                          (Rec (b' (P 0 (Dict c `Product` f)))
                               (b       (Dict c `Product` f)))
  where
  gaddDicts
    = Rec . K1 . baddDicts . unK1 . unRec
  {-# INLINE gaddDicts #-}

-- --------------------------------
-- Instances for base types
-- --------------------------------

instance ConstraintsB Proxy where
  type AllB c Proxy = ()

  baddDicts _ = Proxy
  {-# INLINE baddDicts #-}

instance (ConstraintsB a, ConstraintsB b) => ConstraintsB (Product a b) where
  type AllB c (Product a b) = (AllB c a, AllB c b)

  baddDicts (Pair x y) = Pair (baddDicts x) (baddDicts y)
  {-# INLINE baddDicts #-}

instance (ConstraintsB a, ConstraintsB b) => ConstraintsB (Sum a b) where
  type AllB c (Sum a b) = (AllB c a, AllB c b)

  baddDicts (InL x) = InL (baddDicts x)
  baddDicts (InR x) = InR (baddDicts x)
  {-# INLINE baddDicts #-}

instance ConstraintsB (Const a) where
  type AllB c (Const a) = ()

  baddDicts (Const x) = Const x
  {-# INLINE baddDicts #-}

instance (Functor f, ConstraintsB b) => ConstraintsB (f `Compose` b) where
  type AllB c (f `Compose` b) = AllB c b

  baddDicts (Compose x)
    = Compose (baddDicts <$> x)
  {-# INLINE baddDicts #-}
