{-# OPTIONS --show-implicit --show-irrelevant #-}

module Control.Category.Slice where

open import Level using (suc; _⊔_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Control.Category
open Category using () renaming (Obj to obj; _⇒_ to _▹_⇒_)

-- Given a category C and an object Tgt in C we can define a new category
-- whose objects S are pairs of an object Src in C
-- and a morphism out from Src to Tgt.

record SliceObj {o h} (C : Category o h) (Tgt : obj C) : Set (o ⊔ h)where
  open Category C -- public
  field
    Src : Obj
    out : Src ⇒ Tgt

-- In the following, we fix a category C and an object Tgt.

module _ {o h} {C : Category o h} {Tgt : obj C} where

  -- We use _⇒_ for C's morphisms and _∘_ for their composition.
  open module C = Category C using (_⇒_; _⟫_; _∘_)

  Slice = SliceObj C Tgt
  open module Slice = SliceObj {C = C} {Tgt = Tgt}

  -- A morphism in the slice category of Tgt
  -- from slice (S, s) to (T, t)
  -- is a morphism f : S ⇒ T such that t ∘ f ≡ s.

{-
  record IsTriangle (S : Slice) {T} (t : T ⇒ Tgt) (f : T ⇒ Src S)
      : Set (o ⊔ h)
    where
    constructor triangle

    field
      triangle : out s ∘ f ≡ t
-}

  record SliceMorphism (S T : Slice) : Set h
    where
    constructor sliceMorphism
    field
      mor      : Src S ⇒ Src T
      .triangle : mor ⟫ out T ≡ out S

  open SliceMorphism using (triangle)

  -- We write S ⇉ T for a morphism from slice S to slice T
  _⇉_ = SliceMorphism

  -- The identity slice morphism is just the identity morphism.

  id : ∀ {P} → P ⇉ P
  id = record { mor = C.id; triangle = C.id-first }

  -- The composition of slice morphims is just the composition in C.

  comp : ∀ {S T U} → S ⇉ T → T ⇉ U → S ⇉ U
  comp (sliceMorphism f tri-f) (sliceMorphism g tri-g) = record
    { mor      = f ⟫ g
    ; triangle =  (trans (C.∘-assoc f) (trans (cong (_⟫_ f) tri-g) tri-f))
    }

  ops : CategoryOps (_⇉_)
  ops = record { id = id ; _⟫_ = comp}

  open T-CategoryLaws ops using (T-id-first; T-id-last; T-∘-assoc)


  .id-first : ∀ {S T : Slice} (f : S ⇉ T) → comp id f ≡ f  -- level o ⊔ h
  id-first f = {!C.id-first {g = ?}!}  -- needs cumulativity  (C.id-first is on level h)

{-
  .id-first : T-id-first
  id-first {A = P} {B = Q} {g = pair p β} = begin
      comp id (pair p β)
{-
    ≡⟨⟩
      pair (C.id ⟫ p) (β-pair
        (trans (C.∘-assoc C.id) (trans (cong (_⟫_ C.id) p-fst) C.id-first))
        (trans (C.∘-assoc C.id) (trans (cong (_⟫_ C.id) p-snd) C.id-first)))
-}
    ≡⟨ cong (λ z → pair z (β-pair {!!} {!!})) C.id-first ⟩
      pair p β
    ∎
-}


{-
  .id-first : T-id-first
  id-first {A = P} {B = Q} {g = pair p (β-pair p-fst p-snd)} = begin
      comp id (pair p (β-pair p-fst p-snd))
    ≡⟨⟩
      pair (C.id ⟫ p) (β-pair
        (trans (C.∘-assoc C.id) (trans (cong (_⟫_ C.id) p-fst) C.id-first))
        (trans (C.∘-assoc C.id) (trans (cong (_⟫_ C.id) p-snd) C.id-first)))
    ≡⟨ cong (λ z → pair z (β-pair {!p-fst!} {!!})) C.id-first ⟩
      pair p (β-pair p-fst p-snd)
    ∎
-}
{-
  id-last : ∀ {O P} (f : O ⇉ P) → comp f id ≡ f
  id-last (pair p β) with p ⟫ C.id
  ... | r = ?
-}

{-
  .id-last : ∀ {O P} (f : O ⇉ P) → comp f id ≡ f
  id-last (pair p β) = begin
      comp (pair p β) id
    ≡⟨ cong (λ z → pair z {! isPair (comp (pair p β) id)!}) C.id-last ⟩
      pair p β
    ∎

  sliceIsCategory : IsCategory SliceMorphism
  sliceIsCategory = record
    { ops = ops
    ; laws = record
      { id-first = {!!} -- id-first
      ; id-last = {!!}
      ; ∘-assoc = {!!}
      }
    }

{-
record Pair {o h} {C : Category o h} {A B} (P : SliceObj C A B)
    {X} (f : C ▹ X ⇒ A) (g : C ▹ X ⇒ B) : Set (h ⊔ o)
  where
  open SliceObj P
  field
    ⟨f,g⟩  : C ▹ X ⇒ A×B
    isPair : IsPair P f g ⟨f,g⟩
    unique : ∀ {h} → IsPair P f g h → h ≡ ⟨f,g⟩

  open IsPair isPair public

-- The product of A and B is the terminal object in the SliceCategory

record IsProduct {o h} {C : Category o h} {A B} (P : SliceObj C A B) : Set (h ⊔ o) where
  open Category C
  open SliceObj P
  field
    pairing : ∀ {X} (f : X ⇒ A) (g : X ⇒ B) → Pair P f g

record Product {o h} (C : Category o h) (A B : obj C) : Set (h ⊔ o) where
  field
    slice : SliceObj C A B
    isProduct  : IsProduct slice

  open SliceObj slice public
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
-}
