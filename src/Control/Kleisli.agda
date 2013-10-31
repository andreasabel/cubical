-- The category of monadic functions.

import Relation.Binary.PropositionalEquality

open import Axiom.FunctionExtensionality

open import Control.Monad
open import Control.Category

module Control.Kleisli where

-- The type of monadic functions.

Kleisli : (M : Set → Set) (A : Set) (B : Set) → Set
Kleisli M A B = A → M B

-- The laws of a Kleisli category correspond to the Monad laws,
-- modulo function extensionality.

kleisliIsCategory : {M : Set → Set} (monad : IsMonad M) → IsCategory (Kleisli M)
kleisliIsCategory monad = let open IsMonad monad in record
  { ops = record
    { id  = return
    ; _⟫_ = λ f g a → f a >>= g
    }
  ; laws = record
    { id-first = fun-ext (bind-β _)
    ; id-last  = fun-ext (λ a → bind-η _)
    ; ∘-assoc  = λ f → fun-ext (λ a → bind-assoc (f a))
    }
  }

-- The Kleisli category over a Monad on Set

KLEISLI : {M : Set → Set} (monad : IsMonad M) → Category _ _
KLEISLI monad = record { Mor = Kleisli _; isCategory = kleisliIsCategory monad }
