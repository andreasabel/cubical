module Control.Category where

open import Level using (suc; _⊔_)
open import Relation.Binary.PropositionalEquality

-- Category operations: identity and composition.

module T-CategoryOps {o h} {Obj : Set o} (_⇒_ : Obj → Obj → Set h) where

  T-id = ∀ {A}                            → A ⇒ A
  T-⟫  = ∀ {A B C} (f : A ⇒ B) (g : B ⇒ C) → A ⇒ C
  T-∘  = ∀ {A B C} (g : B ⇒ C) (f : A ⇒ B) → A ⇒ C

record CategoryOps {o h} {Obj : Set o} (_⇒_ : Obj → Obj → Set h)
    : Set (o ⊔ h)
  where
  open T-CategoryOps _⇒_

  infixl 9 _⟫_
  infixr 9 _∘_

  field
    id : T-id
    _⟫_ : T-⟫

  _∘_ : T-∘
  g ∘ f = f ⟫ g

-- Category laws: left and right identity and composition.

module T-CategoryLaws {o h} {Obj : Set o} {_⇒_ : Obj → Obj → Set h}
    (ops : CategoryOps _⇒_)
  where
  open CategoryOps ops public

  T-id-first = ∀ {A B} {g : A ⇒ B} →

    id ⟫ g ≡ g

  T-id-last  = ∀ {A B} {f : A ⇒ B} →

    f ⟫ id ≡ f

  T-∘-assoc  = ∀ {A B C D} (f : A ⇒ B) {g : B ⇒ C} {h : C ⇒ D} →

    (f ⟫ g) ⟫ h ≡ f ⟫ (g ⟫ h)

record CategoryLaws {o h} {Obj : Set o} {_⇒_ : Obj → Obj → Set h}
    (ops : CategoryOps _⇒_) : Set (o ⊔ h)
  where
  open T-CategoryLaws ops

  field
    id-first : T-id-first
    id-last  : T-id-last
    ∘-assoc  : T-∘-assoc

record IsCategory {o h} {Obj : Set o} (_⇒_ : Obj → Obj → Set h) : Set (o ⊔ h) where

  field
    ops  : CategoryOps _⇒_
    laws : CategoryLaws ops

  open CategoryOps  ops  public
  open CategoryLaws laws public

-- The category: packaging objects, morphisms, and laws.

record Category o h : Set (suc (o ⊔ h)) where
   field
     {Obj}      : Set o
     Mor        : Obj → Obj → Set h
     isCategory : IsCategory Mor

   open IsCategory isCategory public


-- Initial object

record IsInitial {o h} {Obj : Set o} (_⇒_ : Obj → Obj → Set h) (Initial : Obj) : Set (h ⊔ o) where
  field
    initial           : ∀ {A}                   → Initial ⇒ A
    initial-universal : ∀ {A} {f : Initial ⇒ A} → f ≡ initial

-- Terminal object

record IsFinal {o h} {Obj : Set o} (_⇒_ : Obj → Obj → Set h) (Final : Obj) : Set (h ⊔ o) where
  field
    final           : ∀ {A}                 → A ⇒ Final
    final-universal : ∀ {A} {f : A ⇒ Final} → f ≡ final
