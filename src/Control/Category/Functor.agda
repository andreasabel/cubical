-- Functors from one category into another

module Control.Category.Functor where

open import Level using (suc; _⊔_)
open import Relation.Binary.PropositionalEquality

open import Control.Category
open Category using () renaming (Obj to obj; Hom to hom)


-- Operations of a functor.

-- Module T-FunctorOps C D F provides notation A ⇒ A' for homset C(A,A')
-- and notation B ⇉ B' for homset D(B,B') and the type T-map for the
-- functorial action.

module T-FunctorOps
  {co ch ce} (C : Category co ch ce)
  {δo dh de} (D : Category δo dh de)
             (F : obj C → obj D)
  where
  open HomSet (hom C) using (_⇒_)
  open HomSet (hom D) using () renaming (_⇒_ to _⇉_)

  -- Type of the map function.
  T-map = ∀ {A B} → (A ⇒ B) → F A ⇉ F B

-- Record FunctorOps C D F can be instantiated to define the functorial action
-- map of F.

record FunctorOps
  {co ch ce} (C : Category co ch ce)
  {δo dh de} (D : Category δo dh de) (F : obj C → obj D) : Set (co ⊔ ch ⊔ ce ⊔ δo ⊔ dh ⊔ de)
  where
  open T-FunctorOps C D F

  -- The functorial action (map function).
  field
    map  : T-map


-- Laws of a functor.

-- Module T-FunctorLaws ops provides notation...

module T-FunctorLaws
  {co ch ce} {C : Category co ch ce}
  {δo dh de} {D : Category δo dh de} {F : obj C → obj D}
  (ops : FunctorOps C D F) where

  open FunctorOps ops public

  open Category C using (_⇒_) renaming
    (Obj to ObjC; id to idC; _∘_ to _∘C_)

  open Category D using (_≈_) renaming
    (Obj to ObjD; _⇒_ to _⇉_; id to idD; _∘_ to _∘D_)

  -- First functor law: identity
  T-map-id = ∀ {A} →

      map (idC {A = A}) ≈ idD

  -- Second functor law: composition.
  T-map-∘  = ∀ {A B C} (f : A ⇒ B) {g : B ⇒ C} →

      map (g ∘C f) ≈ (map g ∘D map f)


record FunctorLaws
  {co ch ce} {C : Category co ch ce}
  {δo dh de} {D : Category δo dh de} {F : obj C → obj D}
  (ops : FunctorOps C D F) : Set ((co ⊔ ch ⊔ ce ⊔ δo ⊔ dh ⊔ de)) where
  open T-FunctorLaws ops

  field
    map-id : T-map-id
    map-∘  : T-map-∘


-- Functoriality.

record IsFunctor
  {co ch ce} {C : Category co ch ce}
  {δo dh de} {D : Category δo dh de} (F : obj C → obj D) : Set (co ⊔ ch ⊔ ce ⊔ δo ⊔ dh ⊔ de) where

  field
    ops  : FunctorOps  C D F
    laws : FunctorLaws ops

  open FunctorOps  ops  public
  open FunctorLaws laws public

-- -}
