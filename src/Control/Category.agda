{-# OPTIONS --without-K #-}

module Control.Category where

open import Level using (suc; _⊔_)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality

-- Module HomSet provides notation A ⇒ B for the Set of morphisms
-- from between objects A and B and names _≈_ and ≈-refl/sym/trans
-- for the equality of morphisms.

module HomSet {o h e} {Obj : Set o} (Hom : Obj → Obj → Setoid h e) where

  _⇒_ : (A B : Obj) → Set h
  A ⇒ B = Setoid.Carrier (Hom A B)

  module _ {A B : Obj} where
    open Setoid (Hom A B) public
      using (_≈_)
      renaming ( isEquivalence to ≈-equiv
               ; refl          to ≈-refl
               ; sym           to ≈-sym
               ; trans         to ≈-trans
               )
{-
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
-}

-- Category operations: identity and composition.

-- Module T-CategoryOps Hom provides the types of
-- identity and composition (forward and backward).

module T-CategoryOps {o h e} {Obj : Set o} (Hom : Obj → Obj → Setoid h e) where

  open HomSet Hom

  T-id = ∀ {A}                            → A ⇒ A
  T-⟫  = ∀ {A B C} (f : A ⇒ B) (g : B ⇒ C) → A ⇒ C
  T-∘  = ∀ {A B C} (g : B ⇒ C) (f : A ⇒ B) → A ⇒ C

-- Record CategoryOps Hom can be instantiated to implement
-- identity and composition for category Hom.

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

-- Module T-CategoryLaws ops provides the types of the laws
-- for the category operations ops.

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

-- Record CategoryLaws ops can be instantiated to prove the laws of the
-- category operations (identity and compositions).

record CategoryLaws {o h e} {Obj : Set o} {Hom : Obj → Obj → Setoid h e}
    (ops : CategoryOps Hom) : Set (o ⊔ h ⊔ e)
  where
  open T-CategoryLaws ops

  field
    id-first : T-id-first
    id-last  : T-id-last
    ∘-assoc  : T-∘-assoc
    ∘-cong   : T-∘-cong

-- Record IsCategory Hom contains the data (operations and laws) to make
-- Hom a category.

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
