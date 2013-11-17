-- The comonad named Store by Russel O'Connor.
-- See his WGP 2011 paper.

{-# OPTIONS --copatterns #-}

module Control.Comonad.Store where

open import Function using (id) renaming (_∘′_ to _∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Axiom.FunctionExtensionality
open import Control.Functor
open import Control.Comonad

record Store (I O : Set) : Set where
  constructor store
  field
    peek : I → O
    pos  : I

  extract : O
  extract = peek pos

{- not in scope: store
  extend′ : ∀ {B} → (Store I O → B) → Store I B
  extend′ f = store (f ∘ store peek) pos
-}

  extend′ : ∀ {B} → (Store I O → B) → Store I B
  pos  (extend′ f) = pos
  peek (extend′ f) = f ∘ s
    where
      s : I → Store I O
      peek (s i) = peek
      pos  (s i) = i

storeIsComonad : ∀ I → IsComonad (Store I)
storeIsComonad I = record
  { extract  = extract
  ; extend   = extend
  ; extend-β = refl
  ; extend-η = refl
  ; extend-∘ = refl
  }
  where
    extract : ∀ {O} → Store I O → O
    extract (store v i) = v i

    extend : ∀ {A B} → (Store I A → B) → Store I A → Store I B
    extend f (store v i) = store (f ∘ store v) i

    extend-β : ∀ {A B} (f : Store I A → B) → extract ∘ extend f ≡ f
    extend-β f = refl

storeIsFunctor : ∀ I → IsFunctor (Store I)
storeIsFunctor I = IsComonad.isFunctor (storeIsComonad I)
