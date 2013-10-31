-- Non-index (plain) monads in form of Kleisli triple.

module Control.Monad where

open import Function using () renaming (_∘′_ to _∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Axiom.FunctionExtensionality
open import Control.Functor

-- The operations of a monad.

module T-MonadOps (M : Set → Set) where

  T-return = ∀ {A}   (a : A)                 → M A
  T-bind   = ∀ {A B} (m : M A) (k : A → M B) → M B


record MonadOps (M : Set → Set) : Set₁ where
  open T-MonadOps M

  infixr 6 _>>=_

  field
    return : T-return
    _>>=_  : T-bind

  bind = _>>=_

  functorOps : FunctorOps M
  functorOps = record
    { _<$>_ = λ f m → m >>= λ a → return (f a)
    }

  open FunctorOps functorOps public


-- The laws of a monad (Kleisli triple variant).

module T-MonadLaws {M : Set → Set} (ops : MonadOps M) where
  open MonadOps ops public

  T-bind-β = ∀ {A B} (k : A → M B) (a : A) →

      return a >>= k  ≡  k a

  T-bind-η = ∀ {A} (m : M A) →

      m >>= return  ≡  m

  T-bind-assoc = ∀ {A B C} (m : M A) {k : A → M B} {l : B → M C} →

      (m >>= k) >>= l  ≡  m >>= λ a → (k a >>= l)

  -- Provable laws.

  -- A variant of bind-β using function extensionality.

  T-bind-β-ext = ∀ {A B C : Set} (f : A → B) (k : B → M C) →

      (λ a → return (f a) >>= k)  ≡  k ∘ f

  T-map-after-bind = ∀ {A B C} (m : M A) {k : A → M B} {f : B → C} →

      f <$> (m >>= k)  ≡  m >>= λ a → f <$> k a

  T-bind-after-map = ∀ {A B C} (m : M A) {k : B → M C} {f : A → B} →

     (f <$> m) >>= k  ≡  m >>= λ a → k (f a)


record MonadLaws {M : Set → Set} (ops : MonadOps M) : Set₁ where
  open T-MonadLaws ops

  -- Axioms.

  field
    bind-β     : T-bind-β
    bind-η     : T-bind-η
    bind-assoc : T-bind-assoc

  -- Derived laws.

  bind-β-ext : T-bind-β-ext
  bind-β-ext f k = fun-ext (λ a → bind-β k (f a))

  map-after-bind : T-map-after-bind
  map-after-bind m = bind-assoc m

  -- A more detailed proof.  (NF: trans (bind-assoc m) refl)
  private
    map-after-bind′ : T-map-after-bind
    map-after-bind′ m {k = k} {f = f} = begin
        f <$> (m >>= k)
      ≡⟨⟩                                        -- definition of map
        ((m >>= k) >>= λ b → return (f b))
      ≡⟨ bind-assoc m ⟩                          -- associativity of bind
        m >>= (λ a → k a >>= λ b → return (f b))
      ≡⟨⟩                                        -- definition of map
        m >>= (λ a → f <$> k a)
      ∎

  bind-after-map : T-bind-after-map
  bind-after-map m {k = k} {f = f} = begin
      (f <$> m) >>= k
    ≡⟨⟩                                        -- definition of map
      (m >>= λ a → return (f a)) >>= k
    ≡⟨ bind-assoc m ⟩                          -- associativity of bind
      m >>= (λ a → return (f a) >>= k)
    ≡⟨ cong (_>>=_ m) (bind-β-ext _ _) ⟩       -- beta for bind
      m >>= (λ a → k (f a))
    ∎

  -- Functor laws.

  open T-FunctorLaws functorOps using (T-map-∘)

  private
    abstract
      map-comp : T-map-∘
      map-comp {f = f} {g = g} m = begin
          g ∘ f <$> m
        ≡⟨⟩
          (m >>= λ a → return (g (f a)))
        ≡⟨ cong (_>>=_ m) (sym (bind-β-ext _ _)) ⟩
          (m >>= λ a → return (f a) >>= λ b → return (g b))
        ≡⟨ sym (bind-assoc m) ⟩
          (m >>= λ a → return (f a)) >>= (λ b → return (g b))
        ≡⟨⟩
          g <$> f <$> m
        ∎

  functorLaws : FunctorLaws functorOps
  functorLaws = record
    { map-id = bind-η
    ; map-∘  = map-comp
    }

  open FunctorLaws functorLaws public


record IsMonad (M : Set → Set) : Set₁ where

  field
    ops  : MonadOps  M
    laws : MonadLaws ops

  open MonadOps  ops  public
  open MonadLaws laws public


{-

-- The operations of a monad.

record MonadOps (M : Set → Set) : Set₁ where

  infixr 6 _>>=_

  T-return = ∀ {A}   (a : A)                 → M A
  T-bind   = ∀ {A B} (m : M A) (k : A → M B) → M B

  field
    return : T-return
    _>>=_  : T-bind

  bind = _>>=_

  functorOps : FunctorOps M
  functorOps = record
    { _<$>_ = λ f m → m >>= λ a → return (f a)
    }

  open FunctorOps functorOps public


-- The laws of a monad (Kleisli triple variant).

record MonadLaws {M : Set → Set} (ops : MonadOps M) : Set₁ where

  open MonadOps ops

  T-bind-β = ∀ {A B} (a : A) (k : A → M B) →

      return a >>= k  ≡  k a

  T-bind-η = ∀ {A} (m : M A) →

      m >>= return  ≡  m

  T-bind-assoc = ∀ {A B C} (m : M A) {k : A → M B} {l : B → M C} →

      (m >>= k) >>= l  ≡  m >>= λ a → (k a >>= l)

  field
    bind-β     : T-bind-β
    bind-η     : T-bind-η
    bind-assoc : T-bind-assoc

  private
    abstract
      map-comp : FunctorLaws.T-map-∘ {!!}
      map-comp = {!!}

  functorLaws : FunctorLaws functorOps
  functorLaws = record
    { map-id = bind-η
    ; map-∘  = {!!}
    }

record IsMonad (M : Set → Set) : Set₁ where




record IsMonad (M : Set → Set) : Set₁ where

  infixr 6 _>>=_

  field
    return : ∀ {A}   (a : A)                 → M A
    _>>=_  : ∀ {A B} (m : M A) (k : A → M B) → M B

    -- Laws

    bind-β : ∀ {A B} (a : A) (k : A → M B) →

      return a >>= k  ≡  k a

    bind-η : ∀ {A} (m : M A) →

      m >>= return  ≡  m

    bind-assoc  : ∀ {A B C} (m : M A) {k : A → M B} {l : B → M C} →

      (m >>= k) >>= l  ≡  m >>= λ a → (k a >>= l)

  bind = _>>=_

  private
    map : Map-T F
    map = λ f m → m >>= λ a → return (f a)

    abstract
      map-comp : Map-Comp-T map

  functor : IsFunctor M
  functor = record
    { _<$>_  = λ f m → m >>= λ a → return (f a)
    ; map-id = bind-η
    ; map-∘  = map-comp
        where x = {!bind-assoc!}
    }
-}
