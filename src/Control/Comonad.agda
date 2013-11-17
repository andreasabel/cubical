-- Non-indexed (plain) monads in form of Kleisli triple, presented in point-free style.

module Control.Comonad where

open import Function using (id) renaming (_∘′_ to _∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Axiom.FunctionExtensionality
open import Control.Functor

record IsComonad (M : Set → Set) : Set₁ where

  -- Methods.

  field
    extract : ∀ {A  } → M A → A
    extend  : ∀ {A B} → (M A → B) → M A → M B

  -- Laws.

  field

    extend-β : ∀ {A B} {k : M A → B} →

      extract ∘ extend k ≡ k

    extend-η : ∀ {A} →

      extend {A = A} extract ≡ id

    extend-∘ : ∀ {A B C} {k : M A → B} {l : M B → C} →

      extend (l ∘ extend k) ≡ extend l ∘ extend k

  -- Comonadic composition.

  comComp : ∀ {A B C : Set} (l : M B → C) (k : M A → B) → (M A → C)
  comComp l k = l ∘ extend k

  -- Functoriality.

  isFunctor : IsFunctor M
  isFunctor = record
    { ops  = record { map = map  }
    ; laws = record { map-id = extend-η ; map-∘ = λ {A B C f g} → sym (map-∘-sym f g) }
    }
    where
      map : ∀ {A B} → (A → B) → M A → M B
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
  field
    M  : Set → Set
    M! : IsComonad M

  open IsComonad M! public
