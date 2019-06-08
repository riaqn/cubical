{-# OPTIONS --cubical --safe #-}
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

pathToIso : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → (I.Iso A B)
pathToIso p = I.iso (transport p) (transport⁻ p) (transportTransport⁻ p) (transport⁻Transport p)

π^≃Ω-group : ∀ {ℓ k} (A :  Pointed {ℓ}) → G.Iso' (π^ k A) (Ω-group k (∥ A ∥' (3 + k)) (isOfHLevel∥∥ {n = 2 + k}))
π^≃Ω-group {k = k} A = G.iso' (pathToIso (cong fst (corollary-7-3-14 {k = 1 + k} {n = 1}))) {!!}

π^≡Ω-group : ∀ {ℓ k} (A :  Pointed {ℓ}) → π^ k A ≡ Ω-group k (∥ A ∥' (3 + k)) (isOfHLevel∥∥ {n = 2 + k})
π^≡Ω-group A = {!!}


π'^-suc : ∀ {ℓ k} {A : Pointed {ℓ}} → (π'^ (suc k) A) ≡ (π'^ k (Ω A))
π'^-suc = {!!}

Ω-≃ : ∀ {ℓ ℓ'} {A : Pointed {ℓ}} {B : Pointed {ℓ'}} → (A P.≃ B) → (Ω A) P.≃ (Ω B)
Ω-≃ f = {!!} , {!!}

Ω^-suc : ∀ {ℓ k} {A : Pointed {ℓ}} → (Ω^ (suc k) A) P.≃ Ω^ k (Ω A)
Ω^-suc {k = 0} = ?
Ω^-suc {k = suc k} {A = A} = Ω-≃ (Ω^-suc {k = k} {A = A})

π^-suc : ∀ {ℓ k} {A : Pointed {ℓ}} → (π^ (suc k) A) G.≃ (π^ k (Ω A))
π^-suc {k = k} {A = A} = f , helper
  where
    f = (U.pathToEquiv (cong (λ x → ∥ x .fst ∥ 2) (Ω^-suc {k = 1 + k})))

    helper : G.isMorph (π^ (suc k) A) (π^ k (Ω A)) (f .fst)
    helper = λ g0 g1 → {!!}



stable : {n k : ℕ} {Sk≤2n : suc k ≤ n * 2} {A : Pointed {ℓ}} (Ac : isConnected n (A .fst) ) → (π^ (suc k ) (Susp' A)) ≡ (π^ k (A))
stable {n = n} {k = k} {A = A} Ac =
  π^ (suc k) (Susp' A) ≡⟨  {!!} ⟩
  π^ k (Ω (Susp' A)) ≡⟨  {!!} ⟩
  Ω-group k (∥ Ω (Susp' A) ∥' (3 + k)) (isOfHLevel∥∥ {n = 2 + k}) ≡⟨ {!cong (Ω-group k)!} ⟩
  Ω-group k (∥ A ∥' (3 + k)) (isOfHLevel∥∥ {n = 2 + k}) ≡⟨ {!!} ⟩
  π^ k A ∎

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

theorem-5-4 : {n : ℕ} {A : Pointed {ℓ}} {Ac : isConnected 2 (A .fst)} {hA : isOfHLevel 3 (A .fst)} → G.Iso (π'^ n (K' n A)) (π'^ zero A)
theorem-5-4 {n = 0} {A = A} {hA = hA} = G.Iso'→Iso (G.iso' (pathToIso (cong (λ x → type (π'^ zero x)) (idemTrunc' hA))) {!!})
theorem-5-4 {n = suc n} {A = A} {Ac = Ac} {hA = hA} = G.compIso {!lemma-5-3 Ac!} (theorem-5-4 {n = n} {A = A} {hA = hA})
  where
    lemma : {l : ℕ} → G.Iso (π'^ (suc l) (K' (suc l) A)) (π'^ (suc l) (Susp'^ l A))
    lemma = G.compIso {!!} {!!}
