-- The category of monadic functions.

open import Level

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Axiom.FunctionExtensionality

open import Control.Monad
open import Control.Category

module Control.Kleisli where

-- The type of monadic functions.

Kleisli : (M : Set → Set) (A : Set) (B : Set) → Set
Kleisli M A B = A → M B

KleisliHom : (M : Set → Set) (A : Set) (B : Set) → Setoid zero zero
KleisliHom M A B = setoid (Kleisli M A B)

-- The laws of a Kleisli category correspond to the Monad laws,
-- modulo function extensionality.

kleisliIsCategory : {M : Set → Set} (monad : IsMonad M) → IsCategory (KleisliHom M)
kleisliIsCategory monad = record
  { ops = record
    { id  = return
    ; _⟫_ = _⟫_
    }
  ; laws = record
    { id-first = fun-ext (bind-β _)
    ; id-last  = fun-ext (λ a → bind-η _)
    ; ∘-assoc  = λ f → fun-ext (λ a → bind-assoc (f a))
    ; ∘-cong   = cong₂ _⟫_
    }
  }
  where
    open IsMonad monad
    open T-CategoryOps (KleisliHom _)
    _⟫_ : T-⟫
    f ⟫ g = λ a → f a >>= g

-- The Kleisli category over a Monad on Set

KLEISLI : {M : Set → Set} (monad : IsMonad M) → Category _ _ _
KLEISLI monad = record { Hom = KleisliHom _; isCategory = kleisliIsCategory monad }
