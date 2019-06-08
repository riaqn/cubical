{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Pointed.Base where

open import Cubical.Foundations.Prelude
import Cubical.Foundations.Equiv as E
import Cubical.Core.Glue as G
open import Cubical.Data.Sigma
import Cubical.Foundations.Univalence as U

Pointed : ∀ {ℓ} → Type (ℓ-suc ℓ)
Pointed {ℓ} = Σ[ A ∈ Type ℓ ] A

_≃_ : ∀ {ℓ ℓ'} → Pointed {ℓ} → Pointed {ℓ'} → Type (ℓ-max ℓ ℓ')
_≃_ A B = Σ[ f ∈ A .fst G.≃ B .fst ] (fst f (A .snd)) ≡ B .snd

ua : ∀ {ℓ} → {A B : Pointed {ℓ}} → A ≃ B → A ≡ B
ua {A = A} {B = B} f = fst Σ≡ ((U.ua (f .fst)) , λ i →
      G.glue (λ  { (i = i0) → snd A
                 ; (i = i1) → snd B }) (f .snd i) )

-- isMorph : {ℓ ℓ' : Level} (A : Pointed {ℓ}) (B : Pointed {ℓ'}) (f : A .fst → B .fst) → Set ℓ'
-- isMorph A B f = f (A .snd) ≡ B .snd

-- Morph : {ℓ ℓ' : Level} (A : Pointed {ℓ}) (B : Pointed {ℓ'}) → Set (ℓ-max ℓ ℓ')
-- Morph A B = Σ (A .fst → B .fst) (isMorph A B)
