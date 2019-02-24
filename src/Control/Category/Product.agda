{-# OPTIONS --show-irrelevant #-}

module Control.Category.Product where

open import Level using (suc; _⊔_)
open import Relation.Binary hiding (_⇒_)

open import Control.Category
open Category using () renaming (Obj to obj; _⇒_ to _▹_⇒_)

-- Pre-Product

-- Given a category C and two objects A, B in C we can define a new category
-- whose objects are triples of an object A×B in C that has
-- morphisms fst, snd to A and B.
-- We call such a triple a pre-product of A and B.
-- Alternatively, it could be called a bislice.

record PreProductObj {o h e} (C : Category o h e) (A B : obj C) : Set (o ⊔ h ⊔ e) where
  open Category C -- public
  field
    A×B : Obj
    fst : A×B ⇒ A
    snd : A×B ⇒ B

-- In the following, we fix a category C and two objects A and B.

module PreProduct {o h e} {C : Category o h e} {A B : obj C} where

  -- We use _⇒_ for C's morphisms and _∘_ for their composition.
  open module C = Category C using (_⇒_; _⟫_; _∘_; _≈_; ≈-refl; ≈-sym; ≈-trans; ∘-cong)

  -- We consider only pre-products of A and B.
  Obj = PreProductObj C A B

  open PreProductObj using () renaming (A×B to A×B◃_)

  -- A morphism in the category of pre-products of A and B
  -- from pre-product (X, f, g) to (A×B, fst, snd)
  -- is a morphism ⟨f,g⟩ : X ⇒ A×B such that fst ∘ ⟨f,g⟩ ≡ f
  -- and snd ∘ ⟨f,g⟩ ≡ g.

  record IsPair (P : Obj) {X} (f : X ⇒ A) (g : X ⇒ B) (⟨f,g⟩ : X ⇒ (A×B◃ P))
      : Set (o ⊔ h ⊔ e)
    where
    constructor β-pair

    open PreProductObj P using (fst; snd)
    field
      β-fst : (fst ∘ ⟨f,g⟩) ≈ f
      β-snd : (snd ∘ ⟨f,g⟩) ≈ g

  record PreProductMorphism (O P : Obj) : Set (o ⊔ h ⊔ e)
    where
    constructor pair

    open PreProductObj O using () renaming (A×B to X; fst to f; snd to g)
    open PreProductObj P
    field
      ⟨f,g⟩   : X ⇒ A×B
      isPair : IsPair P f g ⟨f,g⟩
    open IsPair isPair public

  open PreProductMorphism using (isPair)

  -- We write O ⇉ P for a morphism from pre-product O to pre-product P.
  _⇉_ = PreProductMorphism

  -- The identity pre-product morphism is just the identity morphism.

  id : ∀ {P} → P ⇉ P
  id = record
    { ⟨f,g⟩ = C.id
    ; isPair = record
      { β-fst = C.id-first
      ; β-snd = C.id-first
      }
    }

  -- The composition of pre-product morphims is just the composition in C.

  comp : ∀ {N O P} → N ⇉ O → O ⇉ P → N ⇉ P
  comp (pair o (β-pair o-fst o-snd)) (pair p (β-pair p-fst p-snd)) = record
    { ⟨f,g⟩ = o ⟫ p
    ; isPair = record
      { β-fst = ≈-trans (C.∘-assoc o) (≈-trans (∘-cong ≈-refl p-fst) o-fst)
      ; β-snd = ≈-trans (C.∘-assoc o) (≈-trans (∘-cong ≈-refl p-snd) o-snd)
      }
    }

  -- Thus, we have a category of PreProducts, inheriting the laws from C.

  PreProductHom : (O P : Obj) → Setoid _ _
  PreProductHom O P = record
    { Carrier       = PreProductMorphism O P
    ; _≈_           = λ h i → PreProductMorphism.⟨f,g⟩ h ≈ PreProductMorphism.⟨f,g⟩ i
    ; isEquivalence = record
      { refl  = ≈-refl
      ; sym   = ≈-sym
      ; trans = ≈-trans
      }
    }

  preProductIsCategory : IsCategory PreProductHom
  preProductIsCategory = record
    { ops = record
      { id = id
      ; _⟫_ = comp
      }
    ; laws = record
      { id-first = C.id-first
      ; id-last  = C.id-last
      ; ∘-assoc  = λ f → C.∘-assoc _
      ; ∘-cong   = C.∘-cong
      }
    }

open PreProduct public

{-
record Pair {o h} {C : Category o h} {A B} (P : PreProductObj C A B)
    {X} (f : C ▹ X ⇒ A) (g : C ▹ X ⇒ B) : Set (h ⊔ o)
  where
  open PreProductObj P
  field
    ⟨f,g⟩  : C ▹ X ⇒ A×B
    isPair : IsPair P f g ⟨f,g⟩
    unique : ∀ {h} → IsPair P f g h → h ≈ ⟨f,g⟩

  open IsPair isPair public

-- The product of A and B is the terminal object in the PreProductCategory

record IsProduct {o h} {C : Category o h} {A B} (P : PreProductObj C A B) : Set (h ⊔ o) where
  open Category C
  open PreProductObj P
  field
    pairing : ∀ {X} (f : X ⇒ A) (g : X ⇒ B) → Pair P f g

record Product {o h} (C : Category o h) (A B : obj C) : Set (h ⊔ o) where
  field
    preProduct : PreProductObj C A B
    isProduct  : IsProduct preProduct

  open PreProductObj preProduct public
  open IsProduct isProduct public

{-
record IsProduct {o h} (C : Category o h) (A B A×B : Obj C) : Set (h ⊔ o) where
  open Category C
  field
    fst   : A×B ⇒ A
    snd   : A×B ⇒ B
    pair  : ∀ {X} (f : X ⇒ A) (g : X ⇒ B) → X ⇒ A×B
    β-fst : ∀ {X} {f : X ⇒ A} {g : X ⇒ B} → fst ∘ pair f g ≡ f
    β-snd : ∀ {X} {f : X ⇒ A} {g : X ⇒ B} → fst ∘ pair f g ≡ f

-}

-- Category with Products

HasProducts : ∀ {o h} (C : Category o h) → Set (o ⊔ h)
HasProducts C = ∀ (A B : obj C) → Product C A B




-}
