{-# OPTIONS --copatterns #-}
{-# OPTIONS -v tc.constr.findInScope:15 #-}

-- One-place functors (decorations) on Set

module Control.Bug-Loop where

open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Control.Functor

open IsFunctor {{...}}

record IsDecoration (D : Set → Set) : Set₁ where
  field
    traverse    : ∀ {F} {{ functor : IsFunctor F }} {A B} →

        (A → F B) → D A → F (D B)

    traverse-id : ∀ {A} →

        traverse {F = λ A → A} {A = A} id ≡ id

    traverse-∘  :
      ∀ {F G} {{ funcF : IsFunctor F}} {{ funcG : IsFunctor G}} →
      ∀ {A B C} {f : A → F B} {g : B → G C} →

        traverse ((map g) ∘ f) ≡ map {{funcF}} (traverse g) ∘ traverse f

  isFunctor : IsFunctor D
  isFunctor = record
    { ops   = record { map    = traverse }
    ; laws  = record { map-id = traverse-id
                     ; map-∘  = traverse-∘
                     }
    }

open IsDecoration

idIsDecoration : IsDecoration (λ A → A)
traverse    idIsDecoration f = f
traverse-id idIsDecoration = refl
traverse-∘  idIsDecoration = refl

compIsDecoration : ∀ {D E} → IsDecoration D → IsDecoration E → IsDecoration (λ A → D (E A))
traverse    (compIsDecoration d e) f = traverse d (traverse e f)
traverse-id (compIsDecoration d e) = begin
    traverse d (traverse e id)
  ≡⟨ cong (traverse d) (traverse-id e) ⟩
    traverse d id
  ≡⟨ traverse-id d ⟩
    id
  ∎
traverse-∘ (compIsDecoration d e) {{funcF = funcF}} {{funcG = funcG}} {f = f} {g = g} = begin
    traverse (compIsDecoration d e) (map g ∘ f)
  ≡⟨⟩
    traverse d (traverse e (map g ∘ f))
  ≡⟨ cong (traverse d) (traverse-∘ e) ⟩
    traverse d (map (traverse e g) ∘ traverse e f)
  ≡⟨ traverse-∘ d ⟩
    map (traverse d (traverse e g)) ∘ traverse d (traverse e f)
  ≡⟨⟩
    map (traverse (compIsDecoration d e) g) ∘ traverse (compIsDecoration d e) f
  ∎
