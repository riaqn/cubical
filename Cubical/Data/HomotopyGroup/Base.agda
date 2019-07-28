{-# OPTIONS --cubical --safe #-}
module Cubical.Data.HomotopyGroup.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation
open import Cubical.Foundations.HLevels
open import Cubical.Data.Group as G using (Group)
open import Cubical.Data.Sigma
open import Cubical.Data.Pointed as P using (Pointed) 
import Cubical.Foundations.GroupoidLaws as GL
import Cubical.Foundations.Isomorphism as I
import Cubical.Foundations.Equiv as E
import Cubical.Core.Glue as Gl


Ω : ∀ {ℓ} → Pointed {ℓ} → Pointed {ℓ}
Ω (A , a ) = ( (a ≡ a) , refl)

-- current def. of isOfHLevel could be inconvenient
hLevelΩ : ∀ {ℓ n} → (A : Pointed {ℓ}) (hA : isOfHLevel (2 + n) (A .fst)) → isOfHLevel (1 + n) (Ω A .fst)
hLevelΩ {n = 0} A hA x y = hA _ _ _ _
hLevelΩ {n = suc n} A hA x y = hA _ _ _ _

private
  variable
    ℓ : Level
    X : Type ℓ

iterate : ℕ → (X → X) → X → X
iterate zero f x = x
iterate (suc n) f = λ x → f (iterate n f x)

iterate' : ℕ → (X → X) → X → X
iterate' zero f x = x
iterate' (suc n) f = λ x → iterate' n f (f x)

iterate-lemma : ∀ {n} {f : X → X} {x : X} → f (iterate n f x) ≡ iterate n f (f x)
iterate-lemma {n = 0} = refl
iterate-lemma {n = suc n} {f = f} {x = x} = cong f (iterate-lemma {n = n} {f = f} {x = x})

iterate≡iterate' : ∀ {ℓ} {X : Type ℓ} → iterate {ℓ} {X} ≡ iterate' {ℓ} {X}
iterate≡iterate' = funExt helper
  where
    helper : (n : ℕ) → iterate n ≡ iterate' n
    helper 0 = refl
    helper (suc n) = funExt (λ f → funExt (λ x → iterate-lemma {n = n} {f = f} {x = x} ∙ λ i → helper n i f (f x)))

Ω^ : ℕ → Pointed {ℓ} → Pointed {ℓ}
Ω^ n x = iterate n Ω x

hLevelΩ^ : ∀ {ℓ k n} → (A : Pointed {ℓ}) (hA : isOfHLevel (k + 2 + n) (A .fst)) → isOfHLevel (2 + n) (Ω^ k A .fst)
hLevelΩ^ {k = 0} A hA = hA
hLevelΩ^ {k = suc k} {n = n} A hA = hLevelΩ {n = 1 + n} A' (hLevelΩ^ {k = k} {n = suc n} A (subst (λ x → isOfHLevel x (A .fst)) (sym helper) hA ))
  where
    A' : Pointed
    A' = Ω^ k A

    helper : k + 2 + suc n ≡ suc k + 2 + n
    helper = +-suc _ _

Ω'^ : ℕ → Pointed {ℓ} → Pointed {ℓ}
Ω'^ n x = iterate' n Ω x

Ω^≡Ω'^ : ∀ {ℓ} → Ω^ {ℓ} ≡ Ω'^ {ℓ}
Ω^≡Ω'^ i n x = iterate≡iterate' i n Ω x

π^ : ∀ {ℓ} → ℕ → Pointed {ℓ} → Group {ℓ}
π^ {ℓ} n p = G.group (∥ A ∥ 2) squash g
  where
    n' : ℕ
    n' = suc n

    A : Type ℓ
    A = (Ω^ n') p .fst

    squash : isOfHLevel 2 (∥ A ∥ 2)
    squash = isOfHLevel∥∥ {n = 1}

    g : G.isGroup (∥ A ∥ 2)
    g = G.group-struct e _⁻¹ _⊙_ lUnit rUnit assoc lCancel rCancel
      where
        e : ∥ A ∥ 2
        e = ∣ (Ω^ n') p .snd ∣

        _⁻¹ : ∥ A ∥ 2 → ∥ A ∥ 2
        _⁻¹ = ind {B = λ _ → ∥ A ∥ 2} (λ x → squash) λ a → ∣ sym a ∣ 

        _⊙_ : ∥ A ∥ 2 → ∥ A ∥ 2 → ∥ A ∥ 2
        _⊙_ = ind2 (λ _ _ → squash) λ a₀ a₁ → ∣ a₀ ∙ a₁ ∣  

        lUnit : (a : ∥ A ∥ 2) → (e ⊙ a) ≡ a
        lUnit = ind (λ _ → isProp→isSet (squash _ _))
                (λ a → cong ∣_∣ (sym (GL.lUnit a) ))

        rUnit : (a : ∥ A ∥ 2) → a ⊙ e ≡ a
        rUnit = ind (λ _ → isProp→isSet (squash _ _))
                    (λ a → cong ∣_∣ (sym (GL.rUnit a) ))

        assoc : (a b c : ∥ A ∥ 2) → ((a ⊙ b) ⊙ c) ≡ (a ⊙ (b ⊙ c))
        assoc = ind3 (λ _ _ _ → isProp→isSet (squash _ _))
                (λ a b c → cong ∣_∣ (sym (GL.assoc _ _ _)))

        lCancel : (a : ∥ A ∥ 2) → ((a ⁻¹) ⊙ a) ≡ e
        lCancel = ind (λ _ → isProp→isSet (squash _ _)) 
                  λ a → cong ∣_∣ (GL.lCancel _)

        rCancel : (a : ∥ A ∥ 2) → (a ⊙ (a ⁻¹)) ≡ e
        rCancel = ind (λ _ → isProp→isSet (squash _ _))
                  λ a → cong ∣_∣ (GL.rCancel _)

π'^ : ∀ {ℓ} → ℕ → Pointed {ℓ} → Group {ℓ}
π'^ {ℓ} n p = G.transportGroup (π^ n p) (cong (λ o → ∥ o (suc n) p .fst ∥ 2) Ω^≡Ω'^)

π^≡π'^ : ∀ {ℓ} → π^ {ℓ} ≡ π'^ {ℓ}
π^≡π'^ = funExt λ n → funExt (λ x → G.transportGroup≡ ((cong (λ o → ∥ o (suc n) x .fst ∥ 2) Ω^≡Ω'^)))

Ω^-group : ∀ {ℓ} (k : ℕ) → (A : Pointed {ℓ}) → (hA : isOfHLevel (3 + k) (A .fst)) → Group {ℓ}
Ω^-group k A hA = G.group (Ω^ (1 + k) A .fst) (hLevelΩ^ {k = 1 + k} {n = 0} A (subst (λ x → isOfHLevel x (A .fst)) helper hA)) (G.group-struct refl sym _∙_ (λ _ → sym (GL.lUnit _) ) (λ _ → sym (GL.rUnit _)) (λ _ _ _ → sym (GL.assoc _ _ _)) GL.lCancel GL.rCancel)
  where
    helper : 3 + k ≡ 1 + k + 2 + 0
    helper = cong suc
             (2 + k ≡⟨ +-comm 2 k ⟩
             k + 2 ≡⟨  sym (+-zero _) ⟩
             k + 2 + 0 ∎)

-- truncation of pointed type
∥_∥'_ : (A : Pointed {ℓ}) (n : ℕ) → Pointed {ℓ}
∥ A ∥' n = (∥ A .fst ∥ n , ∣ A .snd ∣)

π^≡Ω^-group : ∀ {ℓ k} (A :  Pointed {ℓ}) → (hA : isOfHLevel (3 + k) (A .fst)) → π^ k A ≡ Ω^-group k A hA
π^≡Ω^-group {k = k} A hA = G.ua ( f , fmorph)
  where
    f : (Group.type (π^ k A))  Gl.≃
        (Group.type (Ω^-group k A hA))
    f = idemTrunc (Group.setStruc (Ω^-group k A hA))

    fmorph : G.isMorph (π^ k A) (Ω^-group k A hA) (f .fst)
    fmorph = ind2 (λ _ _ → hLevelLift {n = 2} 1 (Group.setStruc (Ω^-group k A hA)) _ _) λ _ _ → refl

-- π≡Ω-group∥ : ∀ {ℓ} (A :  Pointed {ℓ}) → π^ 0 A ≡ Ω^-group 0 (∥ A ∥' 3) (isOfHLevel∥∥ {n = 2})
-- π≡Ω-group∥ A = G.ua ({!f!} , {!!})
--   where
--     f : (∥ snd A ≡ snd A ∥ 2) Gl.≃ (∣ A .snd ∣ ≡ ∣ A .snd ∣)
--     f = E.isoToEquiv (I.iso {!!} {!!} {!!} {!!})
--       where
--       intro : ∥ snd A ≡ snd A ∥ 2 → ∣ A .snd ∣ ≡ ∣ A .snd ∣
--       intro = ind (λ _ → isOfHLevel∥∥ {n = 2} _ _) (cong ∣_∣)

--       elim : ∣ A .snd ∣ ≡ ∣ A .snd ∣ → ∥ snd A ≡ snd A ∥ 2
--       elim = {!!}

-- π^≡Ω^-group∥ : ∀ {ℓ k} (A :  Pointed {ℓ}) → π^ k A ≡ Ω^-group k (∥ A ∥' (3 + k)) (isOfHLevel∥∥ {n = 2 + k})
-- π^≡Ω^-group∥ {k = k} A = G.ua ({!!} , {!!})
--   where
--   f : Group.type (π^ k A) Gl.≃
--       Group.type (Ω^-group k (∥ A ∥' (3 + k)) isOfHLevel∥∥)
--   f = {!!}
