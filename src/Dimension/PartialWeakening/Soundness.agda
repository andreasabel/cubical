
module Soundness where

  open import Exception -- using (Except; left; right; _<$>_; _>>=_)
  open import Injective

  -- Semantics given by application to a name in Fin n

  apply : ∀ {n m} (f : PWeak n m) (i : Fin n) → Except E (Fin m)
  apply []       ()
  apply (e ∷ f)  zero    = left e
  apply (e ∷ f)  (suc i) = apply f i
  apply (lift f) zero    = right zero
  apply (lift f) (suc i) = suc <$> apply f i
  apply (weak f) i       = suc <$> apply f i

  -- Proof of injectivity wrt. semantics

  injective : ∀ {n m} (f : PWeak n m) (i j : Fin n) →
    let k = apply f i in
    let l = apply f j in
    IsDefined k → k ≡ l → i ≡ j
  injective []       ()
  injective (e ∷ f) zero    j        () p
  injective (e ∷ f) (suc i) zero     fi p with apply f i
  injective (e ∷ f) (suc i) zero     () p  | left _
  injective (e ∷ f) (suc i) zero     fi () | right a
  injective (e ∷ f) (suc i) (suc j)  fi p = cong suc (injective f i j fi p)
  injective (lift f) zero   zero     fi p = refl
  injective (lift f) zero   (suc j)  fi p with apply f j
  injective (lift f) zero   (suc j)  fi p | left  _ = ⊥-elim (right≢left p)
  injective (lift f) zero   (suc j)  fi p | right l = ⊥-elim (zero≢suc (right-injective _ _ p))
  injective (lift f) (suc i) zero    fi p with apply f i
  injective (lift f) (suc i) zero    fi p | left  e = ⊥-elim (left≢right p)
  injective (lift f) (suc i) zero    fi p | right k = ⊥-elim (suc≢zero (right-injective _ _ p))
  injective (lift f) (suc i) (suc j) fi p = cong suc (injective f i j (map-def-inv _ fi) (map-injective suc-injective _ _ p))
  injective (weak f) i       j       fi p = injective f i j (map-def-inv _ fi) (map-injective suc-injective _ _ p)

  -- Soundness of id

  apply-id : ∀ n (i : Fin n) → apply id i ≡ return i
  apply-id 0       ()
  apply-id (suc n) zero    = refl
  apply-id (suc n) (suc i) with (apply id i) | (apply-id n i)
  apply-id (suc n) (suc i) | .(right i) | refl = refl

  -- Lemma: one inductive step

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

  apply-comp : ∀ {n m l} (f : PWeak n m) (g : PWeak m l) (i : Fin n) →
    apply (comp f g) i ≡ apply f i >>= apply g
  apply-comp [] g ()
  apply-comp (e ∷ f) g zero = refl
  apply-comp (e ∷ f) g (suc i) = apply-comp f g i
--  apply-comp (lift f) (e ∷ g) i = {!!}
  apply-comp (lift f) (e ∷ g) zero = refl
  apply-comp (lift f) (e ∷ g) (suc i) with apply f i
  apply-comp (lift f) (e ∷ g) (suc i) | left e′ = {!!}
  apply-comp (lift f) (e ∷ g) (suc i) | right a = {!!}
  apply-comp (lift f) (lift g) zero = refl
  apply-comp (lift f) (lift g) (suc i) = lift-lift-suc f (apply-comp f g i)
  apply-comp (lift f) (weak g) i = begin

      suc <$> apply (comp (lift f) g) i

    ≡⟨ cong (_<$>_ suc) (apply-comp (lift f) g i) ⟩  -- ind. hyp.

      suc <$> (apply (lift f) i >>= apply g)

    ≡⟨ map-after-bind (apply (lift f) i) ⟩           -- move map

      apply (lift f) i >>= (λ j → suc <$> apply g j)
    ∎
  apply-comp (weak f) g i = {!!}

