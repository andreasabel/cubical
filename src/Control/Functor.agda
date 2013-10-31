-- Functors on Set

module Control.Functor where

open import Function using (id) renaming (_∘′_ to _∘_)
open import Relation.Binary.PropositionalEquality


-- Operations of a functor.

module T-FunctorOps (F : Set → Set) where

  -- Type of the map function.
  T-map = ∀ {A B} → (A → B) → F A → F B


record FunctorOps (F : Set → Set) : Set₁ where
  open T-FunctorOps F

  infixr 5 _<$>_

  -- The map function.
  field
    _<$>_  : T-map

  map = _<$>_


-- Laws of a functor.

module T-FunctorLaws {F : Set → Set} (ops : FunctorOps F) where
  open FunctorOps ops public

  -- First functor law: identity.
  T-map-id = ∀ {A} (m : F A) →

      id <$> m ≡ m

  -- Second functor law: composition.
  T-map-∘  = ∀ {A B C} {f : A → B} {g : B → C} (m : F A) →

      (g ∘ f) <$> m ≡ g <$> (f <$> m)


record FunctorLaws {F : Set → Set} (ops : FunctorOps F) : Set₁ where
  open T-FunctorLaws ops

  field
    map-id : T-map-id
    map-∘  : T-map-∘


-- Functoriality.

record IsFunctor (F : Set → Set) : Set₁ where

  field
    ops  : FunctorOps  F
    laws : FunctorLaws ops

  open FunctorOps  ops  public
  open FunctorLaws laws public







{- STILL NOT SOPHISTICATED ENOUGH

-- Operations of a functor.

record FunctorOps (F : Set → Set) : Set₁ where

  infixl 5 _<$>_

  -- Type of the map function.
  T-map = ∀ {A B} → (A → B) → F A → F B

  -- The map function.
  field
    _<$>_  : T-map

  map = _<$>_


-- Laws of a functor.

record FunctorLaws {F : Set → Set} (ops : FunctorOps F) : Set₁ where

  open FunctorOps ops

  -- First functor law: identity.
  T-map-id = ∀ {A} (m : F A) →

      id <$> m ≡ m

  -- Second functor law: composition.
  T-map-∘  = ∀ {A B C} {f : A → B} {g : B → C} (m : F A) →

      (g ∘ f) <$> m ≡ g <$> (f <$> m)

  field
    map-id : T-map-id
    map-∘  : T-map-∘


-- Functoriality.

record IsFunctor (F : Set → Set) : Set₁ where

  field
    ops  : FunctorOps  F
    laws : FunctorLaws ops

  open FunctorOps  ops  public
  open FunctorLaws laws public
-}







{-
  mkIsFunctor

  infixl 5 _<$>_

  field
    _<$>_  : Map-T F

    map-id : ∀ {A} (m : F A) →

      id <$> m ≡ m

    map-∘  : ∀ {A B C} {f : A → B} {g : B → C} (m : F A) →

      (g ∘ f) <$> m ≡ g <$> (f <$> m)

  map = _<$>_
-}
