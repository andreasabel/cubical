
module Control.Category.Product where

open import Level using (suc; _⊔_)
open import Relation.Binary.PropositionalEquality

open import Control.Category
open Category using () renaming (Obj to obj; _⇒_ to _▹_⇒_)

-- Product

{-
record ProductStructure {o h} {Obj : Set o} (_⇒_ : Obj → Obj → Set h) (A B : Obj) : Set (h ⊔ o) where
  field
    A×B : Obj
    fst   : A×B ⇒ A
    snd   : A×B ⇒ B
-}

record ProductStructure {o h} (C : Category o h) (A B : obj C) : Set (h ⊔ o) where
  open Category C -- public
  field
    A×B : Obj
    fst : A×B ⇒ A
    snd : A×B ⇒ B

open ProductStructure using () renaming (A×B to A×B◃_)

record IsPair {o h} {C : Category o h} {A B} (P : ProductStructure C A B)
    {X} (f : C ▹ X ⇒ A) (g : C ▹ X ⇒ B) (⟨f,g⟩ : C ▹ X ⇒ A×B◃ P): Set (h ⊔ o)
  where
  open Category C
  open ProductStructure P
  field
    β-fst : fst ∘ ⟨f,g⟩ ≡ f
    β-snd : snd ∘ ⟨f,g⟩ ≡ g

{-
record Pair {o h} {C : Category o h} {A B : Obj C} (P : ProductStructure C A B)
    {X : Obj C} (f : C ▹ X ⇒ A) (g : C ▹ X ⇒ B) : Set _
  where
  open ProductStructure P
  field
    ⟨f,g⟩ : X ⇒ A×B
    β-fst : fst ∘ ⟨f,g⟩ ≡ f
    β-snd : snd ∘ ⟨f,g⟩ ≡ g
 -}

record Pair {o h} {C : Category o h} {A B} (P : ProductStructure C A B)
    {X} (f : C ▹ X ⇒ A) (g : C ▹ X ⇒ B) : Set (h ⊔ o)
  where
  open ProductStructure P
  field
    ⟨f,g⟩  : C ▹ X ⇒ A×B
    isPair : IsPair P f g ⟨f,g⟩
    unique : ∀ {h} → IsPair P f g h → h ≡ ⟨f,g⟩

  open IsPair isPair public


record IsProduct {o h} {C : Category o h} {A B} (P : ProductStructure C A B) : Set (h ⊔ o) where
  open Category C
  open ProductStructure P
  field
    pair : ∀ {X} (f : X ⇒ A) (g : X ⇒ B) → Pair P f g

record Product {o h} (C : Category o h) (A B : obj C) : Set (h ⊔ o) where
  field
    productStructure : ProductStructure C A B
    isProduct        : IsProduct productStructure

  open ProductStructure productStructure public
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


