module Util.Equality where

open import Relation.Binary.PropositionalEquality

app-≡ : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} (x : A) → f ≡ g → f x ≡ g x
app-≡ x refl = refl
