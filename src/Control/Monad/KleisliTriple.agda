-- Non-indexed (plain) monads in form of Kleisli triple, presented in point-free style.

module Control.Monad.KleisliTriple where

open import Function using (id) renaming (_∘′_ to _∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Axiom.FunctionExtensionality
open import Control.Functor

record IsKleisliTriple (M : Set → Set) : Set₁ where

  -- Methods.

  field
    return : ∀ {A  } → A → M A
    bind′  : ∀ {A B} → (A → M B) → M A → M B

  -- Laws.

  field

    bind′-β : ∀ {A B} {k : A → M B} →

      bind′ k ∘ return ≡ k

    bind′-η : ∀ {A} →

      bind′ {A = A} return ≡ id

    bind′-∘ : ∀ {A B C} {k : A → M B} {l : B → M C} →

      bind′ (bind′ l ∘ k) ≡ bind′ l ∘ bind′ k

  -- Notations for bind′.

  -- Postfix category-theoretical notation.
  _✶ = bind′

  -- Infix Haskell notation.
  infixl 6 _=<<_
  _=<<_ = bind′

  -- Kleisli composition.

  infixl 6 _<=<_

  _<=<_ : ∀ {A B C : Set} (l : B → M C) (k : A → M B) → (A → M C)
  l <=< k = bind′ l ∘ k

  -- Functoriality.

  isFunctor : IsFunctor M
  isFunctor = record
    { ops  = record { map = map  }
    ; laws = record { map-id = bind′-η ; map-∘ = sym (map-∘-sym _ _) }
    }
    where
      map : ∀ {A B} → (A → B) → M A → M B
      map f = bind′ (return ∘ f)

      map-∘-sym : ∀ {A B C} (f : A → B) (g : B → C) → map g ∘ map f ≡ map (g ∘ f)
      map-∘-sym f g = begin
        map g ∘ map f                            ≡⟨⟩
        bind′ (return ∘ g) ∘ bind′ (return ∘ f)  ≡⟨ sym bind′-∘ ⟩
        bind′ (bind′ (return ∘ g) ∘ return ∘ f)  ≡⟨ cong (λ z → bind′ (z ∘ f)) bind′-β ⟩
        bind′ (return ∘ g ∘ f)                   ≡⟨⟩
        map (g ∘ f)                              ∎

  open IsFunctor isFunctor public

-- Monads in Kleisli Triple presentation.

record KleisliTriple : Set₁ where
  field
    M  : Set → Set
    M! : IsKleisliTriple M

  open IsKleisliTriple M! public
