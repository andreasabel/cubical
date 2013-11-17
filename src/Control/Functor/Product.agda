-- Product of functors

module Control.Functor.Product where

open import Function using (id) renaming (_∘′_ to _∘_)

open import Data.Product using (_×_; _,_; proj₁; proj₂; <_,_>)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Control.Functor

_×̂_ : Functor → Functor → Functor
FF ×̂ GG = functor (λ X → F X × G X) record
  { ops  = record { map    = map    }
  ; laws = record { map-id = map-id
                  ; map-∘  = λ {A}{B}{C}{f}{g} → map-∘ f g
                  }
  }
  where
    open Functor FF using () renaming (F to F; map to mapF; map-id to mapF-id; map-∘ to mapF-∘)
    open Functor GG using () renaming (F to G; map to mapG; map-id to mapG-id; map-∘ to mapG-∘)

    map : ∀ {A B : Set} (f : A → B) (p : F A × G A) → F B × G B
    map f = < mapF f ∘ proj₁ , mapG f ∘ proj₂ >

    map-id : ∀ {A : Set} → map {A = A} id ≡ id
    map-id = begin
      map id                                 ≡⟨⟩
      < mapF id ∘ proj₁ , mapG id ∘ proj₂ >  ≡⟨ cong (λ z → < z ∘ proj₁ , _ >) mapF-id ⟩
      < proj₁ , mapG id ∘ proj₂ >            ≡⟨ cong (λ z → < _ , z ∘ proj₂ >) mapG-id ⟩
      < proj₁ , proj₂ >                      ≡⟨⟩
      id                                     ∎

    map-∘ : ∀ {A B C : Set} (f : A → B) (g : B → C) →  map (g ∘ f) ≡ map g ∘ map f
    map-∘ f g = begin
      map (g ∘ f) ≡⟨⟩
      < mapF (g ∘ f) ∘ proj₁ , mapG (g ∘ f) ∘ proj₂ >       ≡⟨ cong (λ z → < z ∘ proj₁ , _ >) mapF-∘ ⟩
      < mapF g ∘ mapF f ∘ proj₁ , mapG (g ∘ f) ∘ proj₂ >    ≡⟨ cong (λ z → < mapF g ∘ _ , z ∘ proj₂ >) mapG-∘ ⟩
      < mapF g ∘ mapF f ∘ proj₁ , mapG g ∘ mapG f ∘ proj₂ > ≡⟨⟩
      map g ∘ map f
      ∎

