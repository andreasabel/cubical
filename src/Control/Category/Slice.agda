{-# OPTIONS --copatterns #-}

module Control.Category.Slice where

open import Level using (suc; _⊔_)
open import Relation.Binary hiding (_⇒_)

open import Control.Category
open Category using () renaming (Obj to obj)

-- Given a category C and an object Tgt in C we can define a new category
-- whose objects S are pairs of an object Src in C
-- and a morphism out from Src to Tgt.

record SliceObj {o h e} (C : Category o h e) (Tgt : obj C) : Set (o ⊔ h ⊔ e) where
  constructor sliceObj
  open Category C -- public
  field
    Src : Obj
    out : Src ⇒ Tgt

-- In the following, we fix a category C and an object Tgt.

module _ {o h e} {C : Category o h e} {Tgt : obj C} where

  -- We use _⇒_ for C's morphisms and _∘_ for their composition.
  private
    open module C = Category C hiding (id; ops)

    Slice = SliceObj C Tgt
    open module Slice = SliceObj {C = C} {Tgt = Tgt}

  -- A morphism in the slice category into Tgt
  -- from slice (S, s) to (T, t)
  -- is a morphism f : S ⇒ T such that t ∘ f ≡ s.

  record SliceMorphism (S T : Slice) : Set (h ⊔ e)
    where
    constructor sliceMorphism
    field
      mor      : Src S ⇒ Src T
      triangle : (mor ⟫ out T) ≈ out S

  -- Two morphisms in the slice category are equal
  -- iff they are equal in the underlying category C.

  SliceHom : (S T : Slice) → Setoid _ _
  SliceHom S T = record
    { Carrier       = SliceMorphism S T
    ; _≈_           = λ f g → SliceMorphism.mor f ≈ SliceMorphism.mor g
    ; isEquivalence = record
      { refl  = refl
      ; sym   = sym
      ; trans = trans
      }
    } where open IsEquivalence (≈-equiv {Src S} {Src T})

  -- We write S ⇉ T for a morphism from slice S to slice T

  open HomSet SliceHom using () renaming (_⇒_ to _⇉_; _≈_ to _≐_)

  -- The identity slice morphism is just the identity morphism.

  slice-id : ∀ {P} → P ⇉ P
  slice-id = record { mor = C.id; triangle = C.id-first }

  -- The composition of slice morphims is just the composition in C.

  comp : ∀ {S T U} → S ⇉ T → T ⇉ U → S ⇉ U
  comp (sliceMorphism f tri-f) (sliceMorphism g tri-g) = record
    { mor      = f ⟫ g
    ; triangle = ≈-trans (C.∘-assoc f) (≈-trans (C.∘-cong ≈-refl tri-g) tri-f)
    }

  ops : CategoryOps SliceHom
  ops = record { id = slice-id ; _⟫_ = comp}

  sliceIsCategory : IsCategory SliceHom
  sliceIsCategory = record
    { ops = ops
    ; laws = record
      { id-first = C.id-first -- id-first
      ; id-last  = C.id-last
      ; ∘-assoc  = λ f → C.∘-assoc _
      ; ∘-cong   = C.∘-cong
      }
    }

-- The slice category.

module _  {o h e} (C : Category o h e) (Tgt : obj C) where

  module C = Category C

  _/_ : Category (o ⊔ h ⊔ e) (e ⊔ h) e
  _/_ = record
    { Obj = SliceObj C Tgt
    ; Hom = SliceHom
    ; isCategory = sliceIsCategory
    }

  open Category _/_

-- The terminal object in C / Tgt is (Tgt, id).

  terminalSlice : Obj
  terminalSlice = record { Src = Tgt; out = C.id }

  open IsFinal

  isTerminalSlice : IsFinal Hom terminalSlice
  final           isTerminalSlice {sliceObj Src f}
    = sliceMorphism f C.id-last
  final-universal isTerminalSlice {sliceObj Src f} {sliceMorphism g tri}
    = C.≈-trans (C.≈-sym C.id-last) tri

-- The initial object in C / Tgt is (0, initial)

  module _ {⊥ : obj C} (⊥-initial : IsInitial C.Hom ⊥) where

    open IsInitial ⊥-initial
      renaming (initial to abort; initial-universal to abort-unique)

    initialSlice : Obj
    initialSlice = record { Src = ⊥; out = abort }

    open IsInitial

    isInitialSlice : IsInitial Hom initialSlice
    initial           isInitialSlice = sliceMorphism abort abort-unique
    initial-universal isInitialSlice = abort-unique

