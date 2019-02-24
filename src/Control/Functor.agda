-- Functors on Set

module Control.Functor where

open import Function using (id; flip) renaming (_∘′_ to _∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


-- Operations of a functor.

module T-FunctorOps (F : Set → Set) where

  -- Type of the map function.
  T-map = ∀ {A B} → (A → B) → F A → F B
  T-for = ∀ {A B} → F A → (A → B) → F B

record FunctorOps (F : Set → Set) : Set₁ where
  open T-FunctorOps F

  -- The map function.
  field
    map  : T-map

  -- Alternative notations.
  for : T-for
  for = flip map

  infixr 5 _<$>_ _<&>_
  _<$>_ = map
  _<&>_ = for


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

record Functor : Set₁ where
  constructor functor
  field
    F  : Set → Set
    F! : IsFunctor F

  open IsFunctor F! public

-- Id is a functor.

idIsFunctor : IsFunctor (λ A → A)
idIsFunctor = record
  { ops  = record { map = λ f → f }
  ; laws = record { map-id = refl ; map-∘ = refl }
  }

Id : Functor
Id = record { F = λ A → A ; F! = idIsFunctor }

-- Functors compose.

-- open FunctorOps  {{...}}
-- open FunctorLaws {{...}}

compIsFunctor : ∀ {F G} → IsFunctor F → IsFunctor G → IsFunctor (λ A → F (G A))
compIsFunctor f g = record
  { ops  = record { map    = λ h → F.map (G.map h) }
  ; laws = record { map-id = trans (cong F.map G.map-id) F.map-id
                  ; map-∘  = map-comp
                  }
  }
  where
    module F = IsFunctor f
    module G = IsFunctor g

    map-comp : ∀ {A B C} {h : A → B} {i : B → C} →
      F.map (G.map (i ∘ h)) ≡ F.map (G.map i) ∘ F.map (G.map h)
    map-comp {h = h}{i = i} = begin
        F.map (G.map (i ∘ h))
      ≡⟨ cong F.map G.map-∘ ⟩
        F.map (G.map i ∘ G.map h)
      ≡⟨ F.map-∘ ⟩
        F.map (G.map i) ∘ F.map (G.map h)
      ∎

Comp : Functor → Functor → Functor
Comp (functor F F!) (functor G G!) = functor (λ A → F (G A)) (compIsFunctor F! G!)

-- The constant functor.

constIsFunctor : ∀ A → IsFunctor (λ _ → A)
constIsFunctor A = record
  { ops  = record { map = λ f x → x }
  ; laws = record { map-id = refl ; map-∘ = refl }
  }

Const : (A : Set) → Functor
Const A = functor (λ _ → A) (constIsFunctor A)



