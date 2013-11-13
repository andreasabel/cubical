{-# OPTIONS --copatterns #-}

-- One-place functors (decorations) on Set

module Control.Decoration where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Axiom.FunctionExtensionality
open import Control.Functor renaming (idIsFunctor to Id; compIsFunctor to _·_)

open IsFunctor -- {{...}} LOOPS

record IsDecoration (D : Set → Set) : Set₁ where
  field
    traverse    : ∀ {F} (F! : IsFunctor F) {A B} →

        (A → F B) → D A → F (D B)

    traverse-id : ∀ {A} →

        traverse Id {A = A} id ≡ id

    traverse-∘  :
      ∀ {F G} (F! : IsFunctor F) (G! : IsFunctor G) →
      ∀ {A B C} {f : A → F B} {g : B → G C} →

        traverse (F! · G!) ((map F! g) ∘ f) ≡ map F! (traverse G! g) ∘ traverse F! f

  isFunctor : IsFunctor D
  isFunctor = record
    { ops   = record { map    = traverse Id }
    ; laws  = record { map-id = traverse-id
                     ; map-∘  = traverse-∘ Id Id
                     }
    }

open IsDecoration

-- Identity decoration.

idIsDecoration : IsDecoration (λ A → A)
traverse    idIsDecoration F! f  = f
traverse-id idIsDecoration       = refl
traverse-∘  idIsDecoration F! G! = refl


-- Decoration composition.

_•_ : ∀ {D E} → IsDecoration D → IsDecoration E → IsDecoration (λ A → D (E A))

traverse    (d • e) F f = traverse d F (traverse e F f)

traverse-id (d • e) =
  begin
    traverse d Id (traverse e Id id)  ≡⟨ cong (traverse d Id) (traverse-id e) ⟩
    traverse d Id id                  ≡⟨ traverse-id d ⟩
    id
  ∎

traverse-∘ (d • e) F G {f = f} {g = g} =
  begin
    traverse (d • e) FG (map F g ∘ f)                                       ≡⟨⟩
    traverse d FG (traverse e FG (map F g ∘ f))                             ≡⟨ cong (traverse d FG) (traverse-∘ e F G) ⟩
    traverse d FG (map F (traverse e G g) ∘ traverse e F f)                 ≡⟨ traverse-∘ d F G ⟩
    map F (traverse d G (traverse e G g)) ∘ traverse d F (traverse e F f)   ≡⟨⟩
    map F (traverse (d • e) G g) ∘ traverse (d • e) F f
  ∎
  where FG = F · G

-- The instance.

decoration : ∀ {A} → IsDecoration (_×_ A)
-- traverse decoration F f (a , x) = map F (_,_ a) (f x)           -- FAILS BUG WITH record pattern trans!!
traverse decoration F f ax = map F (_,_ (proj₁ ax)) (f (proj₂ ax)) -- WORKS
traverse-id decoration = refl
traverse-∘  decoration F G {f = f} {g = g} = fun-ext λ ax → let (a , x) = ax in
  begin
    traverse decoration FG (map F g ∘ f) (a , x)                        ≡⟨⟩
    map FG (_,_ a) (map F g (f x))                                      ≡⟨⟩
    map F (map G (_,_ a)) (map F g (f x))                               ≡⟨ cong (λ z → z _) (sym (map-∘ F))  ⟩
    map F (map G (_,_ a) ∘ g) (f x)                                     ≡⟨⟩
    map F (λ y → map G (_,_ a) (g y)) (f x)                             ≡⟨⟩
    map F (λ y → traverse decoration G g (a , y)) (f x)                 ≡⟨⟩
    map F (traverse decoration G g ∘ (_,_ a)) (f x)                     ≡⟨ cong (λ z → z _) (map-∘ F) ⟩
    map F (traverse decoration G g) (map F (_,_ a) (f x))               ≡⟨⟩
    map F (traverse decoration G g) (traverse decoration F f (a , x))   ≡⟨⟩
    (map F (traverse decoration G g) ∘ traverse decoration F f) (a , x)
  ∎
  where FG = F · G
