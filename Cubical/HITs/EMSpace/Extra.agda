{-# OPTIONS --cubical #-}
module Cubical.HITs.EMSpace.Extra where

open import Cubical.Data.Nat

open import Cubical.HITs.Truncation
open import Cubical.HITs.Susp

open import Cubical.Data.HomotopyGroup

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
import Cubical.Foundations.Univalence as U

open import Cubical.Data.Group as G using (Group)
open import Cubical.Data.Pointed as P using (Pointed)
import Cubical.Foundations.Isomorphism as I
import Cubical.Foundations.Equiv as E
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma

open G.Group

open import Cubical.Data.Nat.Order

private
  variable
    ℓ : Level

Susp' : (A : Pointed {ℓ}) → Pointed {ℓ}
Susp' A = (Susp (A .fst) , north)

Susp'^ : (n : ℕ) (A : Pointed {ℓ}) → Pointed {ℓ}
Susp'^ n = iterate n Susp'

Susp^ : (n : ℕ) (A : Type ℓ) → Type ℓ
Susp^ n = iterate n Susp


idemTrunc' : {A : Pointed {ℓ}} {n : ℕ} → isOfHLevel (suc n) (A .fst) → ∥ A ∥' (suc n) ≡ A
idemTrunc' {n = 0} hA = P.ua ((idemTrunc hA) , refl)
idemTrunc' {n = suc n} hA = P.ua (idemTrunc hA , refl)

isConnected : (n : ℕ) (A : Type ℓ) → Type ℓ
isConnected n A = isContr (∥ A ∥ n)

private
  variable
    n k : ℕ
    A : Pointed {ℓ}
    Ac : isConnected n (A .fst)
    hA : isOfHLevel 3 (A .fst)

freudenthal-equivalence : (∥ A ∥' (4 + n +  n)) ≡ (∥ Ω ( Susp' A)  ∥' (4 + n + n))
freudenthal-equivalence = {!!}

corollary-7-3-14 : (∥ Ω^ k A ∥' (1 + n)) ≡ Ω^ k (∥ A ∥' (1 + n + k))
corollary-7-3-14 = {!!}

π^-suc : ∀ {ℓ} (k : ℕ) (A : Pointed {ℓ}) → π^ (suc k) A ≡ π^ k (Ω A)


stable : {n k : ℕ} {A : Pointed {ℓ}} (Ac : isConnected n (A .fst) ) → (π^ (2 + (k + k) ) (Susp' A)) ≡ (π^ (1 + (k + k )) A)
stable {n = n} {k = k} {A = A} Ac =
  π^ (suc (suc (k + k))) (Susp' A) ≡⟨  {!π^-suc (suc (k + k)) (Susp' A)!} ⟩
  π^ (suc (k + k)) (Ω (Susp' A)) ≡⟨ π^≡Ω-group∥ {k = suc (k + k)} (Ω (Susp' A)) ⟩
  Ω-group (suc  (k + k)) (∥ Ω (Susp' A) ∥' (3 + (suc (k + k)))) (isOfHLevel∥∥ {n = (2 + suc (k + k))}) ≡⟨ {!cong (Ω-group k)!} ⟩
  Ω-group (suc (k + k)) (∥ A ∥' (4 + (k + k))) (isOfHLevel∥∥ {n = 3 + (k + k)}) ≡⟨ sym (π^≡Ω-group∥ {k = suc (k + k)} A) ⟩
  π^ (suc (k + k)) A ∎
    -- where
    -- X : ∀ {ℓ} (k : ℕ) → Type (ℓ-suc ℓ)
    -- X {ℓ} k = Σ[ A ∈ Pointed {ℓ}] (isOfHLevel (3 + k) (A .fst))

    -- Ω-group' : ∀ {ℓ} (k : ℕ) → X {ℓ} k → Group {ℓ}
    -- Ω-group' {ℓ} k x = Ω-group k (x .fst) (x .snd)

    -- x0 : X k
    -- x0 = (∥ Ω (Susp' A) ∥' (3 + k) , isOfHLevel∥∥ {n = 2 + k})

    -- x1 : X k
    -- x1 = (∥ A ∥' (3 + k) , isOfHLevel∥∥ {n = 2 + k})

    -- p : x0 ≡ x1
    -- p i = {!freudenthal-equivalence!} , {!!}

-- lemma-5-3 : {n k : ℕ} {A : Pointed {ℓ}} (Ac : isConnected n (A .fst) ) → (π^ (2 + k + k ) (Susp'^ (suc n) A)) ≡ (π^ (1 + k + k) (Susp'^ n A))
-- lemma-5-3  {n = n} {k} {A} Ac = π^ (2 + k + k) ((Susp'^ (suc n) A)) ≡⟨ {!!} ⟩
                                
--                                 π'-group {n = 1 + k + k} (Ω (Susp'^ (suc n) A)) ≡⟨ {!!} ⟩
--                                 π'-group {n = 1 + k + k} (∥ Ω (Susp'^ (suc n) A) ∥' {!!}) ≡⟨  {!!} ⟩
--                                 π'-group {n = 1 + k + k} (∥ Susp'^ n A ∥' {!!}) ≡⟨ {!!} ⟩
--                                 π'-group {n = 1 + k + k} (Susp'^ n A) ≡⟨ {!!} ⟩
--                                 π^ (1 + k + k) (Susp'^ n A) ∎
--   where
--   π'-group : {n : ℕ} (A : Pointed {ℓ}) → Group {ℓ}
--   π'-group {n = n} A = G.transportGroup (π'^ n A) (cong fst (corollary-7-3-14 {k = n} {n = 1}))

--   i : ((π'^ (2 + k + k) (Susp'^ (suc n) A)) .type) ≡
--       ((π'^ (1 + k + k) (Susp'^ n A)) .type)
--   i = -- (∥ Ω^ (3 + k + k) (Susp'^ (suc n) A)∥' 2) .fst ≡⟨  cong (λ o → ∥ o (3 + k + k) (Susp'^ (suc n) A) .fst ∥ 2) Ω^≡Ω'^ ⟩
--       -- (∥ Ω'^ (3 + k + k) (Susp'^ (suc n) A) ∥' 2) .fst ≡⟨ refl ⟩
--       -- (∥ Ω'^ (2 + k + k) (Ω (Susp'^ (suc n) A)) ∥' 2) .fst ≡⟨ cong (λ o → ∥ o (2 + k + k) (Ω (Susp'^ (suc n) A)) .fst ∥ 2) (sym Ω^≡Ω'^) ⟩
--       -- (∥ Ω'^ (2 + k + k) (Ω (Susp'^ (suc n) A))∥' 2) .fst ≡⟨ U.ua (corollary-7-3-14 {k = 2 + k + k} {n = 1} .fst) ⟩
--       -- Ω'^ (2 + k + k) (∥(Ω (Susp' (Susp'^ n A)))∥' (4 + k + k)) .fst ≡⟨ cong (λ o → Ω'^ (2 + k + k) o .fst) (sym (freudenthal-equivalence {n = k})) ⟩
--       -- Ω'^ (2 + k + k) (∥ Susp'^ n A ∥' (4 + k + k)) .fst ≡⟨ sym (U.ua (corollary-7-3-14 {k = 2 + k + k} {n = 1} .fst)) ⟩
--       -- (∥ Ω'^ (2 + k + k) (Susp'^ n A) ∥' 2) .fst  ∎
--       {!!}

K' : ℕ → Pointed {ℓ} → Pointed
K' n A = ∥ Susp'^ n A ∥' (3 + n)

theorem-5-4 : {n : ℕ} {A : Pointed {ℓ}} {Ac : isConnected 2 (A .fst)} {hA : isOfHLevel 3 (A .fst)} → (π'^ n (K' n A)) ≡ (π'^ zero A)
theorem-5-4 {n = 0} {A = A} {hA = hA} = {!!}
theorem-5-4 {n = suc n} {A = A} {Ac = Ac} {hA = hA} = {!!}

