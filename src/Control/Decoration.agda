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

  open IsFunctor isFunctor using () renaming (map to dmap; map-∘ to dmap-∘)

  -- Constant traversal.

  traverse-c :  ∀ {A C} (c : C) (l : D A) → C
  traverse-c {C = C} c = traverse (Const C) {B = C} (λ _ → c)

  -- Holds by parametricity (since type C is arbitrary and there is just one c : C given).

  traverse-const : ∀ {A B C} {c : C} (l : D A) →

      traverse (Const C) {B = B} (λ _ → c) l ≡ c

  traverse-const {A = A} {B = B} {C = C} {c = c} l =
    begin
      traverse (Const C) {B = B} (λ _ → c) l ≡⟨ {!!} ⟩
      c
    ∎


   -- Lens structure.  -- TODO: define Contol.Lens

  get : ∀ {A} → D A → A
  get {A = A} = traverse (Const A) {B = A} id

  set : ∀ {A B} → B → D A → D B
  set b = dmap (λ _ → b)

  -- Lens laws.

  -- 1. Get what you set.

  get-set : ∀ {A} {a : A} (l : D A) →

      get (set a l) ≡ a

  get-set {A = A} {a = a} l =
    begin
      get (set a l)                                               ≡⟨⟩
      get (dmap (λ _ → a) l)                                      ≡⟨⟩
      traverse (Const A) id (traverse Id (λ _ → a) l)             ≡⟨⟩
      (map Id (traverse (Const A) id) ∘ traverse Id (λ _ → a)) l  ≡⟨  cong (λ z → z _) (sym (traverse-∘ Id (Const A)))  ⟩
      traverse (Id · Const A) (map Id id ∘ (λ _ → a)) l           ≡⟨⟩
      traverse (Const A) (λ _ → a) l                              ≡⟨ traverse-const _ ⟩
      a
    ∎

  -- 2. Set what you got.

  set-get : ∀ {A} (l : D A) →

      set (get l) l ≡ l

  set-get {A = A} l =
    begin

      set (get l) l               ≡⟨⟩
      dmap (λ _ → get l) l        ≡⟨⟩
      traverse Id (λ _ → get l) l ≡⟨ {!!} ⟩
      l
    ∎

  -- 3. Set twice is set once.

  set-set : ∀ {A} (a b : A) (l : D A) →

    set a (set b l) ≡ set a l

  set-set a b l =
    begin
      set a (set b l)                      ≡⟨⟩
      (dmap (λ _ → a) ∘ dmap (λ _ → b)) l  ≡⟨ cong (λ z → z l) (sym dmap-∘)  ⟩
      dmap ((λ _ → a) ∘ (λ _ → b)) l       ≡⟨⟩
      dmap (λ _ → a) l                     ≡⟨⟩
      set a l
    ∎

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
