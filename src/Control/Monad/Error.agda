open import Function using (id) renaming (_∘′_ to _∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Control.Monad

module Control.Monad.Error (E : Set) where

-- The Error monad.

data Error (A : Set) : Set where
  fail   : (e : E) → Error A
  return : (a : A) → Error A

-- The following are axiliary definitions for the constructor of errorIsMonad.

module Local where

  -- Bind.

  _>>=_ : ∀ {A B} (m : Error A) (k : A → Error B) → Error B
  fail   e >>= k = fail e
  return a >>= k = k a

  bind = _>>=_

  -- Laws of bind.

  beta : ∀ {A B} (k : A → Error B) (a : A) →
    return a >>= k  ≡  k a
  beta k a = refl

  eta :  ∀ {A} (m : Error A) →
    m >>= return  ≡  m
  eta (fail   e) = refl
  eta (return a) = refl

  assoc : ∀ {A B C} (m : Error A) {k : A → Error B} {l : B → Error C} →
    (m >>= k) >>= l  ≡  m >>= λ a → (k a >>= l)
  assoc (fail   e) = refl
  assoc (return a) = refl

open Local public

-- The monad instance of Error.

errorIsMonad : IsMonad Error
errorIsMonad = record
  { ops  = record
    { return = return
    ; _>>=_  = bind
    }
  ; laws = record
    { bind-β     = beta
    ; bind-η     = eta
    ; bind-assoc = assoc
    }
  }
