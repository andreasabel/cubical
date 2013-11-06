module Control.Category where

open import Level using (suc; _⊔_)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality

module HomSet {o h e} {Obj : Set o} (Hom : Obj → Obj → Setoid h e) where

  _⇒_ : (A B : Obj) → Set h
  A ⇒ B = Setoid.Carrier (Hom A B)

  _≈_ : {A B : Obj} → Rel (A ⇒ B) e
  _≈_ {A = A}{B = B} = Setoid._≈_ (Hom A B)

  ≈-equiv : {A B : Obj}  → IsEquivalence (Setoid._≈_ (Hom A B))
  ≈-equiv {A = A}{B = B} = Setoid.isEquivalence (Hom A B)

  ≈-refl  : {A B : Obj}  → Reflexive _≈_
  ≈-refl  {A = A}{B = B} = Setoid.refl (Hom A B)

  ≈-sym   : {A B : Obj}  → Symmetric _≈_
  ≈-sym   {A = A}{B = B} = Setoid.sym (Hom A B)

  ≈-trans : {A B : Obj}  → Transitive _≈_
  ≈-trans {A = A}{B = B} = Setoid.trans (Hom A B)

-- Category operations: identity and composition.

module T-CategoryOps {o h e} {Obj : Set o} (Hom : Obj → Obj → Setoid h e) where

  open HomSet Hom

  T-id = ∀ {A}                            → A ⇒ A
  T-⟫  = ∀ {A B C} (f : A ⇒ B) (g : B ⇒ C) → A ⇒ C
  T-∘  = ∀ {A B C} (g : B ⇒ C) (f : A ⇒ B) → A ⇒ C

record CategoryOps {o h e} {Obj : Set o} (Hom : Obj → Obj → Setoid h e)
    : Set (o ⊔ h ⊔ e)
  where
  open T-CategoryOps Hom

  infixl 9 _⟫_
  infixr 9 _∘_

  field
    id : T-id
    _⟫_ : T-⟫

  _∘_ : T-∘
  g ∘ f = f ⟫ g

-- Category laws: left and right identity and composition.

module T-CategoryLaws {o h e} {Obj : Set o} {Hom : Obj → Obj → Setoid h e}
    (ops : CategoryOps Hom)
  where
  open HomSet Hom public
  open T-CategoryOps Hom public
  open CategoryOps ops public

  T-id-first = ∀ {A B} {g : A ⇒ B} →

    (id ⟫ g) ≈ g

  T-id-last  = ∀ {A B} {f : A ⇒ B} →

    (f ⟫ id) ≈ f

  T-∘-assoc  = ∀ {A B C D} (f : A ⇒ B) {g : B ⇒ C} {h : C ⇒ D} →

    ((f ⟫ g) ⟫ h) ≈ (f ⟫ (g ⟫ h))

  T-∘-cong = ∀ {A B C} {f f′ : A ⇒ B} {g g′ : B ⇒ C} →
    f ≈ f′ → g ≈ g′ → (f ⟫ g) ≈ (f′ ⟫ g′)

record CategoryLaws {o h e} {Obj : Set o} {Hom : Obj → Obj → Setoid h e}
    (ops : CategoryOps Hom) : Set (o ⊔ h ⊔ e)
  where
  open T-CategoryLaws ops

  field
    id-first : T-id-first
    id-last  : T-id-last
    ∘-assoc  : T-∘-assoc
    ∘-cong   : T-∘-cong

record IsCategory {o h e} {Obj : Set o} (Hom : Obj → Obj → Setoid h e) : Set (o ⊔ h ⊔ e) where

  field
    ops  : CategoryOps Hom
    laws : CategoryLaws ops

  open HomSet        Hom public
  open CategoryOps   ops public
  open CategoryLaws laws public

-- The category: packaging objects, morphisms, and laws.

record Category o h e : Set (suc (o ⊔ h ⊔ e)) where
   field
     {Obj}      : Set o
     Hom        : Obj → Obj → Setoid h e
     isCategory : IsCategory Hom

   open IsCategory isCategory public

-- Initial object

record IsInitial {o h e} {Obj : Set o} (Hom : Obj → Obj → Setoid h e) (Initial : Obj) : Set (h ⊔ o ⊔ e) where
  open HomSet Hom
  open T-CategoryOps Hom
  field
    initial           : ∀ {A}                   → Initial ⇒ A
    initial-universal : ∀ {A} {f : Initial ⇒ A} → f ≈ initial

-- Terminal object

record IsFinal {o h e} {Obj : Set o} (Hom : Obj → Obj → Setoid h e) (Final : Obj) : Set (h ⊔ o ⊔ e) where
  open HomSet Hom
  open T-CategoryOps Hom
  field
    final           : ∀ {A}                 → A ⇒ Final
    final-universal : ∀ {A} {f : A ⇒ Final} → f ≈ final


