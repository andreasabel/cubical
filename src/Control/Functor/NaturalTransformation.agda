{-# OPTIONS --copatterns #-}

module Control.Functor.NaturalTransformation where

open import Function using (id; _∘_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Control.Functor using (Functor; module Functor; Const)
open import Control.Category using (Category; module Category)

-- Natural transformations.

IsNatTrans : (F! G! : Functor) →
  let open Functor F! using () renaming (F to F; map to mapF)
      open Functor G! using () renaming (F to G; map to mapG)
  in
      (n : ∀ {A} → F A → G A) → Set₁

IsNatTrans F! G! eta = ∀ {A B} (f : A → B) →
  let open Functor F! using () renaming (F to F; map to mapF)
      open Functor G! using () renaming (F to G; map to mapG)
  in
      eta ∘ mapF f ≡ mapG f ∘ eta

-- Constant-Constant natural transformation.

KKNat : ∀ {A B} (η : A → B) → IsNatTrans (Const A) (Const B) η
KKNat η = λ f → refl


-- Natural transformations (packaged).

record NatTrans (F! G! : Functor) : Set₁ where

  open Functor F! using () renaming (F to F; map to mapF)
  open Functor G! using () renaming (F to G; map to mapG)
  field

    eta    : ∀ {A} → F A → G A

    square : ∀ {A B} (f : A → B) →

        eta ∘ mapF f ≡ mapG f ∘ eta

open NatTrans

-- The identity natural transformation.

Id : ∀ {F! : Functor} → NatTrans F! F!
Id {F! = F!} = record { eta = λ x → x ; square = λ f → refl }

-- Natural transformations compose.

Comp : ∀ {F! G! H! : Functor} → NatTrans F! G! → NatTrans G! H! → NatTrans F! H!
Comp {F! = F!}{G! = G!}{H! = H!} n m = record { eta = nm ; square = snm }
  where
    open Functor F! using () renaming (F to F; map to mapF)
    open Functor G! using () renaming (F to G; map to mapG)
    open Functor H! using () renaming (F to H; map to mapH)

    nm : ∀ {A} → F A → H A
    nm = λ x → eta m (eta n x)

    snm :  ∀ {A B} (f : A → B) →

        nm ∘ mapF f ≡ mapH f ∘ nm

    snm f = begin
        nm ∘ mapF f             ≡⟨⟩
        eta m ∘ eta n ∘ mapF f  ≡⟨ cong (λ z → eta m ∘ z) (square n f) ⟩
        eta m ∘ mapG f ∘ eta n  ≡⟨ cong (λ z → z ∘ eta n) (square m f) ⟩
        mapH f ∘ eta m ∘ eta n  ≡⟨⟩
        mapH f ∘ nm
      ∎

-- Functor category.

FunctorHom : ∀ (F G : Functor) → Setoid _ _
FunctorHom F G = record
  { Carrier       = NatTrans F G
  ; _≈_           = λ n m → ∀ {A} → eta n {A} ≡ eta m {A}
  ; isEquivalence = record
    { refl  = refl
    ; sym   = λ p → sym p
    ; trans = λ p q → trans p q
    }
  }

FUNCTOR : Category _ _ _
FUNCTOR = record
  { Hom = FunctorHom
  ; isCategory = record
    { ops = record
      { id = Id
      ; _⟫_ = Comp
    }
    ; laws = record
      { id-first = refl
      ; id-last  = refl
      ; ∘-assoc  = λ f → refl
      ; ∘-cong   = λ n≡n' m≡m' → cong₂ (λ m n x → m (n x)) m≡m' n≡n' }
    }
  }

