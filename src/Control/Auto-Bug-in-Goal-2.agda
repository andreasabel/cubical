{-# OPTIONS --copatterns #-}

-- One-place functors (decorations) on Set

module Control.Decoration where

open import Function using (id)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Control.Functor


record IsDecoration (D : Set → Set) : Set₁ where
  field
    traverse : ∀ {F} {{ functor : IsFunctor F }} {A B} → (A → F B) → D A → F (D B)
    traverse-id : ∀ {A} → traverse {F = λ A → A} {A = A} id ≡ id

  isFunctor : IsFunctor D
  isFunctor = record
    { ops  = record { map = traverse }
    ; laws = record { map-id = traverse-id ; map-∘ = {!!} } }

open IsDecoration

idIsDecoration : IsDecoration (λ A → A)
traverse idIsDecoration f = f
traverse-id idIsDecoration = {!!}

compIsDecoration : ∀ {D E} → IsDecoration D → IsDecoration E → IsDecoration (λ A → D (E A))
traverse (compIsDecoration d e) f = traverse d (traverse e f)
traverse-id (compIsDecoration d e) = {!!}
