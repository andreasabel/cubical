{-# OPTIONS --without-K #-}

import Level

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Control.Category

module Dimension.PartialWeakening (E : Set) where

-- Partial weakenings from n to m are injective maps from Fin n to Fin m
-- that can raise exceptions in E.

data PWeak : (n m : ℕ) → Set where
  []   :                                   PWeak 0 0              -- empty
  _∷_  : ∀ {n m} (e : E) (f : PWeak n m) → PWeak (1 + n) m        -- partial
  lift : ∀ {n m}         (f : PWeak n m) → PWeak (1 + n) (1 + m)  -- new name
  weak : ∀ {n m}         (f : PWeak n m) → PWeak n (1 + m)        -- unused n.

-- Empty.

empty : ∀ {m} → PWeak 0 m
empty {m = 0}     = []
empty {m = suc m} = weak (empty {m = m})

-- Identity.

id : ∀ {n} → PWeak n n
id {n = 0}     = []
id {n = suc n} = lift (id {n = n})

-- Composition.

comp : ∀ {n m l} → PWeak n m → PWeak m l → PWeak n l
comp []        _       = empty
comp (e ∷ f)   g       = e ∷ comp f g
comp (lift f) (e ∷ g)  = e ∷ comp f g
comp (lift f) (lift g) = lift (comp f g)
comp (lift f) (weak g) = weak (comp (lift f) g)
comp (weak f) (e ∷ g)  = comp f g
comp (weak f) (lift g) = weak (comp f g)
comp (weak f) (weak g) = weak (comp (weak f) g)

module Laws where

  -- Empty is initial (i.e., equal to any (g : PWeak 0 m))

  abstract
    empty-extensional : ∀ {m} (g : PWeak 0 m) → g ≡ empty
    empty-extensional []       = refl
    empty-extensional (weak g) = cong weak (empty-extensional g)

  -- Empty is left dominant

  abstract
    empty-comp : ∀ {n m} (g : PWeak n m) → comp empty g ≡ empty
    empty-comp g = empty-extensional (comp empty g)
{-
    empty-comp [] = refl
    empty-comp (e ∷ g) = empty-comp g
    empty-comp (lift g) = cong weak (empty-comp g)
    empty-comp {n = zero } (weak g) = refl
    empty-comp {n = suc n} (weak g) = cong weak (empty-comp g)
-}
  -- Left identity.

  abstract
    left-id : ∀ {n m} (g : PWeak n m) → comp id g ≡ g
    left-id             []       = refl
    left-id             (e ∷ g)  = cong (_∷_ e) (left-id g)
    left-id             (lift g) = cong lift (left-id g)
    left-id {n = zero}  (weak g) = cong weak (sym (empty-extensional g))
    left-id {n = suc n} (weak g) = cong weak (left-id g)

  -- Right identity.

  abstract
    right-id : ∀ {n m} (g : PWeak n m) → comp g id ≡ g
    right-id             []       = refl
    right-id             (e ∷ g)  = cong (_∷_ e) (right-id g)
    right-id             (lift g) = cong lift (right-id g)
    right-id {n = zero } (weak g) = cong weak (right-id g)
    right-id {n = suc n} (weak g) = cong weak (right-id g)

  -- Associativity.

  abstract
    assoc : ∀ {n m l k} (f : PWeak n m) (g : PWeak m l) (h : PWeak l k) →
      comp (comp f g) h ≡ comp f (comp g h)
    assoc []        g        h       = empty-extensional _
    assoc (e ∷ f)   g        h       = cong (_∷_ e) (assoc f g h)
    assoc (lift f) (e ∷ g)   h       = cong (_∷_ e) (assoc f g h)
    assoc (lift f) (lift g) (e ∷ h)  = cong (_∷_ e) (assoc f g h)
    assoc (lift f) (lift g) (lift h) = cong lift (assoc f g h)
    assoc (lift f) (lift g) (weak h) = cong weak (assoc (lift f) (lift g) h)
    assoc (lift f) (weak g) (e ∷ h)  = assoc (lift f) g h
    assoc (lift f) (weak g) (lift h) = cong weak (assoc (lift f) g h)
    assoc (lift f) (weak g) (weak h) = cong weak (assoc (lift f) (weak g) h)
    assoc (weak f) (e ∷ g)   h       = assoc f g h
    assoc (weak f) (lift g) (e ∷ h)  = assoc f g h
    assoc (weak f) (lift g) (lift h) = cong weak (assoc f g h)
    assoc (weak f) (lift g) (weak h) = cong weak (assoc (weak f) (lift g) h)
    assoc (weak f) (weak g) (e ∷ h)  = assoc (weak f) g h
    assoc (weak f) (weak g) (lift h) = cong weak (assoc (weak f) g h)
    assoc (weak f) (weak g) (weak h) = cong weak (assoc (weak f) (weak g) h)

open Laws

-- PWeak is a category with initial object

pWeakIsCategory : IsCategory PWeak
pWeakIsCategory = record
  { ops  = record
    { id  = id
    ; _⟫_ = comp
    }
  ; laws = record
    { id-first = left-id _
    ; id-last  = right-id _
    ; ∘-assoc  = λ f → assoc f _ _
    }
  }

emptyIsInitial : IsInitial PWeak 0
emptyIsInitial = record
  { initial = empty
  ; initial-universal = empty-extensional _
  }

-- The category PWEAK

PWEAK : Category _ _
PWEAK = record { Mor = PWeak; isCategory = pWeakIsCategory }
