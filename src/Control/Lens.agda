module Control.Lens where

open import Function using (id; _∘_; const; flip)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Axiom.FunctionExtensionality
open import Control.Functor renaming (Comp to _•_)
open import Control.Functor.NaturalTransformation renaming (Id to Nid; Comp to _·_)

-- S-combinator.

apply : ∀ {A B C : Set} → (A → B → C) → (A → B) → A → C
apply f g a = f a (g a)

-- Flipped S-combinator (flipped apply).

flipply : ∀ {O A B : Set} → (A → O → B) → (O → A) → O → B
flipply f g o = f (g o) o

app-≡ : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} (x : A) → f ≡ g → f x ≡ g x
app-≡ x refl = refl

record GetSetLens (O I : Set) : Set where

  -- Operations.

  field
    get : O → I
    set : I → O → O

  -- Laws.

  field
    set-set : ∀ {i j} → set i ∘ set j   ≡ set i
    get-set : ∀ {i}   → get ∘ set i     ≡ const i
    set-get :           flipply set get ≡ id      -- ∀ {o} → set (get o) o ≡ o


-- A variant of GetSetLens

record GetsModifyLens (O I : Set) : Set₁ where

  -- Operations.

  field
    gets   : ∀ {J} → (I → J) → O → J
    modify : (I → I) → O → O

  -- Laws.

  field
    -- modify is an endofunctor in the discrete category I.

    modify-id     :

      modify id ≡ id

    modify-∘ : ∀ {f g} →

      modify g ∘ modify f ≡ modify (g ∘ f)

    -- Free theorem for gets.

    gets-free     : ∀ {J K} {f : J → K} (g : I → J) →

      f ∘ gets g ≡ gets (f ∘ g)

    gets-modify   : ∀ {J} {f : I → I} {g : I → J} →

      gets g ∘ modify f ≡ gets (g ∘ f)

    -- set (get o) o ≡ o
    -- modify (const (gets id o)) o ≡ o
    -- modify (const (gets f  o)) o ≡ modify f o
    -- modify (λ i → g (gets f o) i) o ≡ modify (λ i → g i (f i)) o
    -- apply (flip modify) (g ∘ gets f) ≡ modify (apply g f)

    modify-gets   : ∀ {J} {g : I → J} (s : J → I → I) →

      flipply modify (s ∘ gets g) ≡ modify (flipply s g)

  getSetLens : GetSetLens O I
  getSetLens = record
    { get     = gets id
    ; set     = modify ∘ const
    ; set-set = modify-∘
    ; get-set = get-set
    ; set-get = set-get
    }
    where
      get : O → I
      get = gets id

      set : I → O → O
      set = modify ∘ const

      get-set : ∀ {i} → get ∘ set i ≡ const i
      get-set {i} =
        begin
          get ∘ set i                ≡⟨⟩
          gets id ∘ modify (const i) ≡⟨ gets-modify ⟩
          gets (id ∘ const i)        ≡⟨⟩
          gets (const i ∘ id)        ≡⟨ sym (gets-free id)  ⟩
          const i ∘ get              ≡⟨⟩
          const i
        ∎

      set-get : flipply set get ≡ id
      set-get = begin
        flipply set get                     ≡⟨⟩
        flipply (modify ∘ const) (gets id)  ≡⟨⟩
        flipply modify (const ∘ gets id)    ≡⟨ modify-gets const ⟩
        modify (flipply const id)           ≡⟨⟩
        modify id                           ≡⟨ modify-id ⟩
        id                                  ∎

  open GetSetLens getSetLens public


-- van Laarhoven lenses

record Lens (O I : Set) : Set₁ where

  -- Single operation: Functorial modify.
  field
    modify! : ∀ (FF : Functor) → let F = Functor.F FF in
      (I → F I) → (O → F O)

  -- Laws
  -- 0. Free theorem:
  field

    modify!-free : (FF GG : Functor) (N : NatTrans FF GG) →

      let open Functor FF using () renaming (F to F; map to mapF) in
      let open Functor GG using () renaming (F to G; map to mapG) in
      let open NatTrans N using () renaming (eta to η) in

      (f : I → F I) →

        η ∘ modify! FF f ≡ modify! GG (η ∘ f)

  -- 1. Identity law:  -- Generalize?

    modify!-id :

        modify! Id id ≡ id

  -- 2. Composition law:

    modify!-∘ : (FF GG : Functor) →

      let open Functor FF using () renaming (F to F; map to mapF) in
      let open Functor GG using () renaming (F to G; map to mapG) in

      {f : I → F I} →
      {g : I → G I} →

        mapF (modify! GG g) ∘ modify! FF f

          ≡  modify! (FF • GG) (mapF g ∘ f)

  getsModifyLens : GetsModifyLens O I
  getsModifyLens  = record
    { gets        = gets
    ; modify      = modify
    ; modify-id   = modify!-id
    ; modify-∘    = modify-∘
    ; gets-free   = λ {J}{K}{f} g → gets-free f g
    ; gets-modify = gets-modify
    ; modify-gets = modify-gets
    }
    where

    -- gets and modify

      gets : ∀ {J} → (I → J) → (O → J)
      gets {J = J} = modify! (Const J)

      modify : (I → I) → O → O
      modify = modify! Id

      -- Laws of gets and modify.

      modify-∘ : ∀ {f g} → modify g ∘ modify f ≡ modify (g ∘ f)
      modify-∘ = modify!-∘ Id Id

      gets-free : ∀ {J K} (f : J → K) (g : I → J) → f ∘ gets g ≡ gets (f ∘ g)
      gets-free {J = J}{K = K} f g = modify!-free (Const J) (Const K) (ConstNat f) g

      gets-modify : ∀ {J} {f : I → I} {g : I → J} →
        gets g ∘ modify f ≡ gets (g ∘ f)
      gets-modify {J = J} = modify!-∘ Id (Const J)

      modify-gets : ∀ {J} {g : I → J} (s : J → I → I) →
        flipply modify (s ∘ gets g) ≡ modify (flipply s g)
      modify-gets = {!!}  -- TODO! Difficult.

  open GetsModifyLens getsModifyLens public

-- Every GetSetLens is a van Laarhoven lens ??

lensFromGetSet : ∀ {O I} → GetSetLens O I → Lens O I
lensFromGetSet {O = O}{I = I} l = record
  { modify!      = modify!
  ; modify!-free = {!!}
  ; modify!-id   = set-get
  ; modify!-∘    = modify!-∘
  }
  where
    open GetSetLens l

    module Define-modify! (FF : Functor) where
      open Functor FF

      modify! : (I → F I) → (O → F O)
      modify! f = apply (map ∘ flip set) (f ∘ get)

      derivation-of-modify : ∀ f → modify! f ≡ apply (map ∘ flip set) (f ∘ get)
      derivation-of-modify f = begin
        modify! f
        ≡⟨⟩  (λ o → map (λ i → set i o) (f (get o)))
        ≡⟨⟩  (λ o → ((λ o → map (λ i → set i o)) o) ((f ∘ get) o))
        ≡⟨⟩  apply (λ o → map (λ i → set i o)) (f ∘ get)
        ≡⟨⟩  apply (λ o → map (flip set o)) (f ∘ get)
        ≡⟨⟩  apply (map ∘ flip set) (f ∘ get)
        ∎
    open Define-modify!

{-
    modify! FF f = apply (map ∘ flip set) (f ∘ get)
      where open Functor FF
      modify! :  ∀ (FF : Functor) → let F = Functor.F FF in
        (I → F I) → (O → F O)
    -- modify! FF f o = map (λ i → set i o) (f (get o))
    -- modify! FF f = λ o → ((λ o → map (λ i → set i o)) o) ((f ∘ get) o)
    -- modify! FF f = apply (λ o → map (λ i → set i o)) (f ∘ get)
    -- modify! FF f = apply (λ o → map (flip set o)) (f ∘ get)
    modify! FF f = apply (map ∘ flip set) (f ∘ get)
      where open Functor FF
-}

    modify!-free : (FF GG : Functor) (N : NatTrans FF GG) →

      let open Functor FF using () renaming (F to F; map to mapF) in
      let open Functor GG using () renaming (F to G; map to mapG) in
      let open NatTrans N using () renaming (eta to η) in

      (f : I → F I) →

        η ∘ modify! FF f ≡ modify! GG (η ∘ f)

    modify!-free FF GG N f = fun-ext λ o → begin

        η (modify! FF f o)                       ≡⟨⟩

        η (mapF (λ i → set i o) (f (get o)))     ≡⟨ app-naturality (flip set) (f ∘ get) o ⟩

        mapG (λ i → set i o) (η (f (get o)))     ≡⟨⟩

        modify! GG (η ∘ f) o                     ∎

      where
        open Functor FF using () renaming (F to F; map to mapF; map-∘ to mapF-∘)
        open Functor GG using () renaming (F to G; map to mapG; map-∘ to mapG-∘)
        open NatTrans N using (app-naturality) renaming (eta to η)


    modify!-id : modify! Id id ≡ id
    modify!-id = fun-ext λ o → begin
      (Functor.map Id) (λ i → set i o) (id (get o))  ≡⟨⟩
      (λ i → set i o) (get o)                        ≡⟨⟩
      set (get o) o                                  ≡⟨⟩
      flipply set get o                              ≡⟨ app-≡ o set-get ⟩
      id o                                           ≡⟨⟩
      o                                              ∎

    modify!-∘ : (FF GG : Functor) →

      let open Functor FF using () renaming (F to F; map to mapF) in
      let open Functor GG using () renaming (F to G; map to mapG) in

      {f : I → F I} →
      {g : I → G I} →

        mapF (modify! GG g) ∘ modify! FF f

          ≡  modify! (FF • GG) (mapF g ∘ f)

    modify!-∘ FF GG {f = f} {g = g} = fun-ext λ o → begin

      mapF (modify! GG g) (modify! FF f o)                           ≡⟨⟩

      mapF  (λ o → mapG (λ i → set i o) (g (get o)))
                  (mapF (λ i → set i o) (f (get o)))                 ≡⟨ app-≡ _ (sym mapF-∘) ⟩

      mapF ((λ o → mapG (λ i → set i o) (g (get o)))
                      ∘ (λ i → set i o))(f (get o))                  ≡⟨⟩

      mapF (λ j → mapG (λ i → set i (set j o)) (g (get (set j o))))
           (f (get o))                                               ≡⟨ {!set-set!} ⟩

      mapF (λ j → mapG (λ i → set i o) (g (get (set j o))))
           (f (get o))                                               ≡⟨ {!get-set!} ⟩

      mapF (λ j → mapG (λ i → set i o) (g j))
           (f (get o))                                               ≡⟨⟩

      mapF (mapG (λ i → set i o) ∘ g) (f (get o))                    ≡⟨ app-≡ _ mapF-∘ ⟩

      mapF (mapG (λ i → set i o)) (mapF g (f (get o)))               ≡⟨⟩

      mapFG (λ i → set i o) (mapF g (f (get o)))                     ≡⟨⟩

      modify! (FF • GG) (mapF g ∘ f) o                               ∎

      where
        open Functor FF using () renaming (F to F; map to mapF; map-∘ to mapF-∘)
        open Functor GG using () renaming (F to G; map to mapG; map-∘ to mapG-∘)
        mapFG = Functor.map (FF • GG)
{-
  Lens operations:

    get : Lens I O → O → I
    get l o = l (mapK I) id o

    set : Len I O → I → O → O
    set l i o = l mapId (const i) o

  Lens laws:

  a. set-set

       set l i ∘ set l j = set l i

     Prove from 2.

  b. get-set

       get l (set l i o) = i

     Prove from 0. + 2.

  c. set-get

     set l o (get l o) = o

       This states that set is surjective, it is equivalent to

     ∀ o → ∃₂ λ i o′ → set l o′ i = o

  Independence of 0, 1, 2.
  -----------------------

  A. 0 does not imply 2.  Counterexample:

    -- An impossible lens, since ⊤ contains nothing, especially not Bool

    l : Lens Bool ⊤
    l map f = map (const tt) (f true)

      ( get l _   = false )
      ( set l _ _ = tt    )

    does not satisfy 2.  (Lens composition)

      mapId (l (mapK Bool) id) ∘ l mapId not
    = const ((mapK Bool) (const tt) true)
    = const true

      l (mapK Bool) (id ∘ not)
    = const ((mapK Bool) (const tt) (not true)
    = const false

  B. 0, 2 are not sufficent to prove c.  Counterexample:

    -- Lens focusing on nothing.

    l : Lens ⊤ Bool

    l map f _ = map (const true) (f tt)

      ( get l _   = tt   )
      ( set l _ _ = true )
      so,  set l false (get l false) /= false

    Proof of 2:




-}
