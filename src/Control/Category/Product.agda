
module Control.Category.Product where

open import Level using (suc; _⊔_)
open import Relation.Binary.PropositionalEquality

open import Control.Category
open Category using () renaming (Obj to obj; _⇒_ to _▹_⇒_)

-- Pre-Product

-- Given a category C and two objects A, B in C we can define a new category
-- whose objects are triples of an object A×B in C that has
-- morphisms fst, snd to A and B.
-- We call such a triple a pre-product of A and B.

record PreProductObj {o h} (C : Category o h) (A B : obj C) : Set (o ⊔ h)where
  open Category C -- public
  field
    A×B : Obj
    fst : A×B ⇒ A
    snd : A×B ⇒ B

open PreProductObj using () renaming (A×B to A×B◃_)

module PreProduct {o h} {C : Category o h} {A B : obj C} where
  open Category C

-- A morphism in the category of pre-products of A and B
-- from pre-product (X, f, g) to (A×B, fst, snd)
-- is a morphism ⟨f,g⟩ : X ⇒ A×B such that fst ∘ ⟨f,g⟩ ≡ f
-- and snd ∘ ⟨f,g⟩ ≡ g.

record IsPair {o h} {C : Category o h} {A B} (P : PreProductObj C A B)
    {X} (f : C ▹ X ⇒ A) (g : C ▹ X ⇒ B) (⟨f,g⟩ : C ▹ X ⇒ A×B◃ P): Set (o ⊔ h)
  where
  open Category C
  open PreProductObj P
  field
    β-fst : fst ∘ ⟨f,g⟩ ≡ f
    β-snd : snd ∘ ⟨f,g⟩ ≡ g

record PreProductMorphism {o h} {C : Category o h} {A B : obj C}
  (O P : PreProductObj C A B) : Set (o ⊔ h)
  where
  open Category C
  open PreProductObj O using () renaming (A×B to X; fst to f; snd to g)
  open PreProductObj P
  field
    ⟨f,g⟩  : X ⇒ A×B
    isPair : IsPair P f g ⟨f,g⟩
  open IsPair isPair public

preProductIsCategory : ∀ {o h} {C : Category o h} {A B : obj C} →
  IsCategory {Obj = PreProductObj C A B} PreProductMorphism
preProductIsCategory {C = C} = record
  { ops = record
    { id = record
      { ⟨f,g⟩ = id
      ; isPair = record { β-fst = id-first; β-snd = id-first }
      }
    ; _⟫_ = λ O P → record { ⟨f,g⟩ = {!!}; isPair = {!!} }
    }
  ; laws = record
    { id-first = {!!}
    ; id-last = {!!}
    ; ∘-assoc = {!!}
    }
  }
  where open Category C

record Pair {o h} {C : Category o h} {A B} (P : PreProductObj C A B)
    {X} (f : C ▹ X ⇒ A) (g : C ▹ X ⇒ B) : Set (h ⊔ o)
  where
  open PreProductObj P
  field
    ⟨f,g⟩  : C ▹ X ⇒ A×B
    isPair : IsPair P f g ⟨f,g⟩
    unique : ∀ {h} → IsPair P f g h → h ≡ ⟨f,g⟩

  open IsPair isPair public

-- The product of A and B is the terminal object in the PreProductCategory

record IsProduct {o h} {C : Category o h} {A B} (P : PreProductObj C A B) : Set (h ⊔ o) where
  open Category C
  open PreProductObj P
  field
    pair : ∀ {X} (f : X ⇒ A) (g : X ⇒ B) → Pair P f g

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


