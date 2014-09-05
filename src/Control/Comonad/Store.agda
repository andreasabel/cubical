-- The comonad named Store by Russel O'Connor.
-- See his WGP 2011 paper.

{-# OPTIONS --copatterns #-}

module Control.Comonad.Store where

open import Function using (id) renaming (_∘′_ to _∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Axiom.FunctionExtensionality
open import Util.Equality

open import Control.Functor
open import Control.Functor.NaturalTransformation
open import Control.Comonad

-- The Store comonad.

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

StoreC : ∀ I → Comonad
StoreC I = comonad (Store I) (storeIsComonad I)

-- Functoriality,

storeIsFunctor : ∀ I → IsFunctor (Store I)
storeIsFunctor I = IsComonad.isFunctor (storeIsComonad I)

StoreF : (I : Set) → Functor
StoreF I = functor (Store I) (storeIsFunctor I)

idLens : ∀ {I} → I → Store I I
idLens = store id

-- Van Laarhoven presentation

record LStore (I O : Set) : Set₁ where
  -- constructor lstore
  field
    modifier : (FF : Functor) → let open Functor FF in
               (I → F I) → F O

  -- Laws.

  -- 0. Free theorem.
  field
    modifier-free : {FF GG : Functor} (N : NatTrans FF GG) →
      let open Functor FF using () renaming (F   to F) in
      let open Functor GG using () renaming (F   to G) in
      let open NatTrans N using () renaming (eta to η) in
      (f : I → F I) →

        η (modifier FF f) ≡ modifier GG (η ∘ f)

  -- 1. Identity

  -- modifier-id :

-- Converting between store comonads.

storeToLStore : ∀ {I O} → Store I O → LStore I O
storeToLStore {I = I} {O = O} (store v i) = record
  { modifier      = modifier
  ; modifier-free = modifier-free
  }
  where
    modifier : (FF : Functor) → let open Functor FF in
               (I → F I) → F O
    modifier FF f = map v (f i)
      where open Functor FF

    modifier-free : {FF GG : Functor} (N : NatTrans FF GG) →
      let open Functor FF using () renaming (F   to F) in
      let open Functor GG using () renaming (F   to G) in
      let open NatTrans N using () renaming (eta to η) in
      (f : I → F I) →

        η (modifier FF f) ≡ modifier GG (η ∘ f)

    modifier-free {FF = FF}{GG = GG} N f = begin
        η (modifier FF f)   ≡⟨⟩
        (η ∘ mapF v) (f i)  ≡⟨ app-≡ (f i) (naturality _) ⟩
        (mapG v ∘ η) (f i)  ≡⟨⟩
        modifier GG (η ∘ f) ∎

      where
        open Functor FF using () renaming (F to F; map to mapF; map-id to mapF-id; map-∘ to mapF-∘)
        open Functor GG using () renaming (F to G; map to mapG; map-id to mapG-id; map-∘ to mapG-∘)
        open NatTrans N using (naturality) renaming (eta to η)

lstoreToStore : ∀ {I O} → LStore I O → Store I O
lstoreToStore {I = I} {O = O} l = LStore.modifier l (StoreF I) idLens

-- Isomorphism.

storeId : ∀ {I O} (s : Store I O) → lstoreToStore (storeToLStore s) ≡ s
storeId {I = I}{O = O} (store v i) = begin
  lstoreToStore (storeToLStore (store v i))                      ≡⟨⟩
  LStore.modifier (storeToLStore (store v i)) (StoreF I) idLens  ≡⟨⟩
  Functor.map (StoreF I) v (idLens i)                            ≡⟨⟩
  Functor.map (StoreF I) v (store id i)                          ≡⟨⟩
  store (v ∘ id) i                                               ≡⟨⟩
  store v i ∎

-- BAD IDEA: the proof of modifier-free should not be compared with ≡

lstoreId : ∀ {I O} (l : LStore I O) → storeToLStore (lstoreToStore l) ≡ l
lstoreId {I = I}{O = O} l = begin
   storeToLStore (lstoreToStore l)             ≡⟨⟩
   storeToLStore (modifier (StoreF I) idLens)  ≡⟨⟩
   storeToLStore (modifier (StoreF I) idLens)  ≡⟨ {!!} ⟩
   l                                           ∎
  where open LStore l
