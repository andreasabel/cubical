module Axiom.FunctionExtensionality where

open import Level using (zero)
open import Relation.Binary.PropositionalEquality

postulate
  fun-ext : Extensionality zero zero
