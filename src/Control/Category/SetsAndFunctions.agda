-- Category of sets and functions

module Control.Category.SetsAndFunctions where

open import Level using (zero; suc; _⊔_)
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Axiom.FunctionExtensionality

open import Control.Category
open import Control.Category.Product

-- Category SET

Functions : Set → Set → Set
Functions A B = A → B

setIsCategory : IsCategory Functions
setIsCategory = record
  { ops = record
    { id  = λ x → x
    ; _⟫_ = λ f g x → g (f x)
    }
  ; laws = record
    { id-first = refl
    ; id-last  = refl
    ; ∘-assoc  = λ f → refl
    }
  }

SET : Category _ _
SET = record { _⇒_ = Functions; isCategory = setIsCategory }


timesProductStructure : (A B : Set) → ProductStructure SET A B
timesProductStructure A B = record
  { A×B = A × B
  ; fst = proj₁
  ; snd = proj₂
  }

⟨_,_⟩ :  {A B C : Set} (f : C → A) (g : C → B) → C → A × B
⟨ f , g ⟩ = λ x → f x , g x

pairIsPair : {A B C : Set} (f : C → A) (g : C → B) →
  IsPair (timesProductStructure A B) f g ⟨ f , g ⟩
pairIsPair f g = record
  { β-fst = refl
  ; β-snd = refl
  }

open IsPair

pairPair : {A B C : Set} (f : C → A) (g : C → B) →
  Pair (timesProductStructure A B) f g
pairPair f g = record
  { ⟨f,g⟩  = ⟨ f , g ⟩
  ; isPair = pairIsPair f g
  ; unique =  λ p → fun-ext (λ x → cong₂ (λ f g → f x , g x) (β-fst p) (β-snd p))
  }

timesIsProduct : (A B : Set) → Product SET A B
timesIsProduct A B = record
  { productStructure = timesProductStructure A B
  ; isProduct = record { pair = pairPair }
  }
