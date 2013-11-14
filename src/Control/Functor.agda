-- Functors on Set

module Control.Functor where

open import Function using (id) renaming (_∘′_ to _∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


-- Operations of a functor.

module T-FunctorOps (F : Set → Set) where

  -- Type of the map function.
  T-map = ∀ {A B} → (A → B) → F A → F B


record FunctorOps (F : Set → Set) : Set₁ where
  open T-FunctorOps F

  -- The map function.
  field
    map  : T-map

  infixr 5 _<$>_
  _<$>_ = map


-- Laws of a functor.

module T-FunctorLaws {F : Set → Set} (ops : FunctorOps F) where
  open FunctorOps ops public

  -- First functor law: identity.     ∀ (m : F A) → id <$> m ≡ m
  T-map-id = ∀ {A : Set} →

      map {A = A} id ≡ id

  -- Second functor law: composition. ∀ (m : F A) → (g ∘ f) <$> m ≡ g <$> (f <$> m)
  T-map-∘  = ∀ {A B C} {f : A → B} {g : B → C} →

      map (g ∘ f) ≡ map g ∘ map f

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

-- Id is a functor.

idIsFunctor : IsFunctor (λ A → A)
idIsFunctor = record
  { ops  = record { map = λ f → f }
  ; laws = record { map-id = refl ; map-∘ = refl }
  }

-- Functors compose.

open FunctorOps  {{...}}
open FunctorLaws {{...}}

compIsFunctor : ∀ {F G} → IsFunctor F → IsFunctor G → IsFunctor (λ A → F (G A))
compIsFunctor f g = record
  { ops  = record { map    = λ h → map (map h) }
  ; laws = record { map-id = trans (cong F.map map-id) map-id
                  ; map-∘  = map-comp
                  }
  }
  where
    open module F = IsFunctor f using (ops; laws)
    open module G = IsFunctor g using (ops; laws)

    map-comp : ∀ {A B C} {h : A → B} {i : B → C} →
      F.map (G.map (i ∘ h)) ≡ F.map (G.map i) ∘ F.map (G.map h)
    map-comp {h = h}{i = i} = begin
        F.map (G.map (i ∘ h))
      ≡⟨ cong F.map map-∘ ⟩
        F.map (G.map i ∘ G.map h)
      ≡⟨ map-∘ ⟩
        F.map (G.map i) ∘ F.map (G.map h)
      ∎

-- The constant functor.

Const : ∀ A → IsFunctor (λ _ → A)
Const A = record
  { ops  = record { map = λ f x → x }
  ; laws = record { map-id = refl ; map-∘ = refl }
  }




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
