-- Non-indexed (plain) monads in form of Kleisli triple, presented in point-free style.

module Control.Comonad where

open import Function using (id) renaming (_∘′_ to _∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Axiom.FunctionExtensionality
open import Control.Functor

record IsComonad (W : Set → Set) : Set₁ where

  -- Methods.

  field
    extract : ∀ {A  } → W A → A
    extend  : ∀ {A B} → (W A → B) → W A → W B

  -- Laws.

  field

    extend-β : ∀ {A B} {k : W A → B} →

      extract ∘ extend k ≡ k

    extend-η : ∀ {A} →

      extend {A = A} extract ≡ id

    extend-∘ : ∀ {A B C} {k : W A → B} {l : W B → C} →

      extend (l ∘ extend k) ≡ extend l ∘ extend k

  -- Comonadic composition.

  comComp : ∀ {A B C : Set} (l : W B → C) (k : W A → B) → (W A → C)
  comComp l k = l ∘ extend k

  -- Functoriality.

  isFunctor : IsFunctor W
  isFunctor = record
    { ops  = record { map = map  }
    ; laws = record { map-id = extend-η ; map-∘ = λ {A B C f g} → sym (map-∘-sym f g) }
    }
    where
      map : ∀ {A B} → (A → B) → W A → W B
      map f = extend (f ∘ extract)

      map-∘-sym : ∀ {A B C} (f : A → B) (g : B → C) → map g ∘ map f ≡ map (g ∘ f)
      map-∘-sym f g = begin
        map g ∘ map f                                ≡⟨⟩
        extend (g ∘ extract) ∘ extend (f ∘ extract)  ≡⟨ sym extend-∘ ⟩
        extend (g ∘ extract ∘ extend (f ∘ extract))  ≡⟨ cong (λ z → extend (g ∘ z)) extend-β ⟩
        extend (g ∘ f ∘ extract)                     ≡⟨⟩
        map (g ∘ f)                                  ∎

  open IsFunctor isFunctor public

-- Monads in Kleisli Triple presentation.

record Comonad : Set₁ where
  constructor comonad
  field
    W  : Set → Set
    W! : IsComonad W

  open IsComonad W! public

-- Casting a Comonad to a Functor

FunctorOfComonad : Comonad → Functor
FunctorOfComonad WW = functor W isFunctor
  where open Comonad WW
