{-# OPTIONS --copatterns #-}
{-# OPTIONS --show-implicit #-}

-- One-place functors (decorations) on Set

module Control.Decoration where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (id; _∘_; const)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Axiom.FunctionExtensionality
open import Control.Functor hiding (Id; Const) renaming (idIsFunctor to Id; compIsFunctor to _·_; constIsFunctor to Const)
open import Control.Functor.NaturalTransformation using (IsNatTrans; KKNat)

open IsFunctor -- {{...}} LOOPS

record IsDecoration (D : Set → Set) : Set₁ where
  field
    traverse    : ∀ {F} (F! : IsFunctor F) {A B} →

        (A → F B) → D A → F (D B)

    -- The free theorem for traverse:
    -- A natural transformation after a traversal can be combined with the traversal.

    traverse-free : ∀ {F} (F! : IsFunctor F) {G} (G! : IsFunctor G) →
      ∀ (η : ∀ {A} → F A → G A) (η! : IsNatTrans (functor F F!) (functor G G!) η) →
      ∀ {A B} (f : A → F B) →

        η ∘ traverse F! f ≡ traverse G! (η ∘ f)

    -- Identity traversal.

    traverse-id : ∀ {A} →

        traverse Id {A = A} id ≡ id

    -- Distributing a traversal.

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


   -- Lens structure.  -- TODO: define Contol.Lens

  gets : ∀ {A B} → (A → B) → D A → B
  gets {B = B} = traverse (Const B) {B = B}

  get : ∀ {A} → D A → A
  get = gets id

  set : ∀ {A B} → B → D A → D B
  set b = dmap (const b)

  -- Law: gets in terms of get.
  gets=∘get : ∀ {A B} (f : A → B) →

      gets f ≡ f ∘ get

  gets=∘get {A = A}{B = B} f =
    begin
      gets f
        ≡⟨⟩
      traverse (Const B) {B = B} f
        ≡⟨ traverse-∘ (Const B) Id {g = f} ⟩
      traverse (Const B) {B = A} f
        ≡⟨ sym (traverse-free (Const A) (Const B) f (KKNat f) id) ⟩
      f ∘ traverse (Const A) {B = A} id
        ≡⟨⟩
      f ∘ get
    ∎

  -- Constant traversal.

  traverse-c :  ∀ {A B} (b : B) (l : D A) → B
  traverse-c {B = B} b = traverse (Const B) {B = B} (const b)

  -- Holds by parametricity (since type B is arbitrary and there is just one b : B given).

  traverse-const : ∀ {A B} {b : B} (l : D A) →

      traverse (Const B) (const b) l ≡ b

  traverse-const {A = A} {B = B} {b = b} l =
    begin
      traverse (Const B) (const b) l               ≡⟨ cong (λ z → z l) (gets=∘get (const b)) ⟩
      (const b ∘ traverse (Const A) {B = B} id) l  ≡⟨⟩
      b
    ∎

  -- Lens laws.

  -- 1. Get what you set.

  get-set : ∀ {A} {a : A} →

      get ∘ set {A = A} a ≡ const a

  get-set {A = A} {a = a} =
    begin
      get ∘ set a                                             ≡⟨⟩
      get ∘ dmap (const a)                                    ≡⟨⟩
      traverse (Const A) id ∘ traverse Id (const a)           ≡⟨⟩
      map Id (traverse (Const A) id) ∘ traverse Id (const a)  ≡⟨ sym (traverse-∘ Id (Const A)) ⟩
      traverse (Id · Const A) (map Id id ∘ const a)           ≡⟨⟩
      traverse (Const A) (const a)                            ≡⟨⟩
      gets (const a)                                          ≡⟨ gets=∘get (const a) ⟩
      const a ∘ get                                           ≡⟨⟩
      const a
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

  set-set : ∀ {A} (a b : A) →

    set a ∘ set {A = A} b  ≡  set a

  set-set a b =
    begin
      set a ∘ set b                    ≡⟨⟩
      dmap (const a) ∘ dmap (const b)  ≡⟨ sym dmap-∘ ⟩
      dmap (const a ∘ const b)         ≡⟨⟩
      dmap (const a)                   ≡⟨⟩
      set a
    ∎

open IsDecoration


-- Identity decoration.

idIsDecoration : IsDecoration (λ A → A)
traverse      idIsDecoration F! f         = f
traverse-free idIsDecoration F! G! η η! f = refl
traverse-id   idIsDecoration              = refl
traverse-∘    idIsDecoration F! G!        = refl


-- Decoration composition.

_•_ : ∀ {D E} → IsDecoration D → IsDecoration E → IsDecoration (λ A → D (E A))

traverse    (d • e) F f = traverse d F (traverse e F f)

traverse-free (d • e) F G η η! f =
  begin
    η ∘ traverse (d • e) F f    ≡⟨⟩
    η ∘ traverse d F (traverse e F f)    ≡⟨  traverse-free d F G η η! _ ⟩
    traverse d G (η ∘ traverse e F f)    ≡⟨  cong (traverse d G) (traverse-free e F G η η! f) ⟩
    traverse d G (traverse e G (η ∘ f))  ≡⟨⟩
    traverse (d • e) G (η ∘ f)
  ∎

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
traverse      decoration F f ax              = map F (_,_ (proj₁ ax)) (f (proj₂ ax)) -- WORKS

traverse-free decoration F G η η! f          =  fun-ext λ ax → let (a , x) = ax in
  begin
    (η ∘ traverse decoration F f) (a , x)  ≡⟨⟩
    (η ∘ map F (_,_ a)) (f x)              ≡⟨  cong (λ z → z (f x)) (η! (_,_ a))  ⟩
    (map G (_,_ a) ∘ η) (f x)              ≡⟨⟩
    map G (_,_ a) (η (f x))                ≡⟨⟩
    traverse decoration G (η ∘ f) (a , x)
  ∎

traverse-id   decoration                     = refl

traverse-∘    decoration F G {f = f} {g = g} = fun-ext λ ax → let (a , x) = ax in
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

