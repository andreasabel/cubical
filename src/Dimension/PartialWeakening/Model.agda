-- Interpretation of partial weakenings as partial finite maps.

module Dimension.PartialWeakening.Model (E : Set) where

import Level

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Axiom.FunctionExtensionality

open import Control.Category
open import Control.Category.Functor

open import Control.Kleisli
open import Control.Monad using (IsMonad; module IsMonad)
import Control.Monad.Error as Err
open module Error = Err E using (Error; fail; return; errorIsMonad)

-- open import Dimension.PartialWeakening E  -- horrible names
import Dimension.PartialWeakening as PW
open module PWeak = PW E

open IsMonad errorIsMonad hiding (return)
module Kl = IsCategory (kleisliIsCategory errorIsMonad)

-- Semantics given by application to a name in Fin n

apply : ∀ {n m} (f : PWeak n m) (i : Fin n) → Error (Fin m)
apply []       ()
apply (e ∷ f)  zero    = fail e
apply (e ∷ f)  (suc i) = apply f i
apply (lift f) zero    = return zero
apply (lift f) (suc i) = suc <$> apply f i
apply (weak f) i       = suc <$> apply f i

-- Soundness of id

abstract
  apply-id : ∀ n (i : Fin n) → apply id i ≡ return i
  apply-id 0       ()
  apply-id (suc n) zero    = refl
  apply-id (suc n) (suc i) with (apply id i) | (apply-id n i)
  apply-id (suc n) (suc i) | .(return i) | refl = refl

-- Lemma: one inductive step

abstract
  lift-lift-suc : ∀ {n m l} (f : PWeak n m) {g : PWeak m l} {i : Fin n} →

    (ih : apply (comp f g) i ≡ apply f i >>= apply g) →

    apply (comp (lift f) (lift g)) (suc i)  ≡
    apply (lift f) (suc i) >>= apply (lift g)

  lift-lift-suc f {g = g} {i = i} ih = begin

      apply (comp (lift f) (lift g)) (suc i)

    ≡⟨⟩                                      -- definition of comp

      apply (lift (comp f g)) (suc i)

    ≡⟨⟩                                      -- definition of apply

      suc <$> apply (comp f g) i

    ≡⟨ cong (_<$>_ suc) ih ⟩                 -- induction hypothesis

      suc <$> (apply f i >>= apply g)

    ≡⟨ map-after-bind (apply f i) ⟩          -- map commutes with bind I

      (apply f i >>= λ j → suc <$> apply g j)

    ≡⟨⟩                                      -- definition of apply

      (apply f i >>= λ j → apply (lift g) (suc j))

    ≡⟨ sym (bind-after-map (apply f i)) ⟩    -- map commutes with bind II

      (suc <$> apply f i) >>= apply (lift g)

    ≡⟨⟩                                      -- definition of apply

      apply (lift f) (suc i) >>= apply (lift g)
    ∎

-- Soundness of comp

abstract
  apply-comp : ∀ {n m l} (f : PWeak n m) (g : PWeak m l) (i : Fin n) →

   apply (comp f g) i ≡ apply f i >>= apply g

  apply-comp [] g ()
  apply-comp (e ∷ f) g zero = refl
  apply-comp (e ∷ f) g (suc i) = apply-comp f g i
  apply-comp (lift f) (e ∷ g) zero = refl
  apply-comp (lift f) (e ∷ g) (suc i) rewrite apply-comp f g i with apply f i
  ... | fail e′  = refl
  ... | return j = refl
  apply-comp (lift f) (lift g) zero = refl
  apply-comp (lift f) (lift g) (suc i) = lift-lift-suc f (apply-comp f g i)
  apply-comp (lift f) (weak g) i = begin

      suc <$> apply (comp (lift f) g) i

    ≡⟨ cong (_<$>_ suc) (apply-comp (lift f) g i) ⟩  -- ind. hyp.

      suc <$> (apply (lift f) i >>= apply g)

    ≡⟨ map-after-bind (apply (lift f) i) ⟩           -- move map

      apply (lift f) i >>= (λ j → suc <$> apply g j)
    ∎

  apply-comp (weak f) (e ∷ g) i rewrite apply-comp f g i = sym (bind-after-map (apply f i))

  apply-comp (weak f) (lift g) i rewrite apply-comp f g i = begin

      suc <$> (apply f i >>= apply g)

    ≡⟨ map-after-bind (apply f i) ⟩

      apply f i >>= (λ j → suc <$> apply g j)

    ≡⟨⟩

      apply f i >>= (λ j → apply (lift g) (suc j))

    ≡⟨ sym (bind-after-map (apply f i)) ⟩

      (suc <$> apply f i) >>= apply (lift g)
    ∎

  apply-comp (weak f) (weak g) i rewrite apply-comp (weak f) g i =
    map-after-bind (apply (weak f) i)

-- The Kleisli category of partial finite maps  Fin n → Error (Fin m)

PFin : (n m : ℕ) → Set
PFin n m = Fin n → Error (Fin m)

pFinIsCategory : IsCategory PFin
pFinIsCategory = record
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

PFIN : Category _ _
PFIN = record { Mor = PFin; isCategory = pFinIsCategory }

-- The evaluation functor

-- ⟦_⟧ : ∀ {n m} → PWeak n m → PFin n m
-- ⟦ f ⟧ = apply f

applyIsFunctor : IsFunctor {C = PWEAK} {D = PFIN} (λ n → n)
applyIsFunctor = record
  { ops  = record
    { map = apply
    }
  ; laws = record
    { map-id = fun-ext (apply-id _)
    ; map-∘  = λ f → fun-ext (apply-comp f _)
    }
  }

