-- Functors from one category into another

module Control.Category.Functor where

open import Level using (suc; _⊔_)
open import Relation.Binary.PropositionalEquality

open import Control.Category
open Category using (Obj; Mor)


-- Operations of a functor.

module T-FunctorOps
  {co ch} (C : Category co ch)
  {do dh} (D : Category do dh)
          (F : Obj C → Obj D)
  where

  _⇒_ = Mor C
  _⇉_ = Mor D

  -- Type of the map function.
  T-map = ∀ {A B} → (A ⇒ B) → F A ⇉ F B


record FunctorOps
  {co ch} (C : Category co ch)
  {do dh} (D : Category do dh)
          (F : Obj C → Obj D) : Set (co ⊔ ch ⊔ do ⊔ dh)
  where
  open T-FunctorOps C D F

  -- The functorial action (map function).
  field
    map  : T-map


-- Laws of a functor.

module T-FunctorLaws
  {co ch} {C : Category co ch}
  {do dh} {D : Category do dh} {F : Obj C → Obj D} (ops : FunctorOps C D F) where

  open FunctorOps ops public

  open Category C using () renaming
    (Obj to ObjC; Mor to _⇒_; id to idC; _∘_ to _∘C_)

  open Category D using () renaming
    (Obj to ObjD; Mor to _⇉_; id to idD; _∘_ to _∘D_)

  -- First functor law: identity
  T-map-id = ∀ {A} →

      map (idC {A = A}) ≡ idD

  -- Second functor law: composition.
  T-map-∘  = ∀ {A B C} (f : A ⇒ B) {g : B ⇒ C} →

      map (g ∘C f) ≡ map g ∘D map f


record FunctorLaws
  {co ch} {C : Category co ch}
  {do dh} {D : Category do dh} {F : Obj C → Obj D} (ops : FunctorOps C D F) : Set ((co ⊔ ch ⊔ do ⊔ dh)) where
  open T-FunctorLaws ops

  field
    map-id : T-map-id
    map-∘  : T-map-∘


-- Functoriality.

record IsFunctor
  {co ch} {C : Category co ch}
  {do dh} {D : Category do dh} (F : Obj C → Obj D) : Set (co ⊔ ch ⊔ do ⊔ dh) where

  field
    ops  : FunctorOps  C D F
    laws : FunctorLaws ops

  open FunctorOps  ops  public
  open FunctorLaws laws public

