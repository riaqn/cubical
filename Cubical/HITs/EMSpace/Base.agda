{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.EMSpace.Base where
open import Cubical.Data.Group
open import Cubical.Core.Prelude hiding (comp)
open import Cubical.Data.HomotopyGroup

open Group
open isGroup

data EMSpace1 {ℓ} (G : Group {ℓ}) : Set ℓ where
  base : EMSpace1 G
  loop : G .type → (base ≡ base)
  loop-id : loop (G .groupStruc .id) ≡ refl
  loop-comp : ∀ (g h : G .type) → loop (G .groupStruc .comp g h) ≡ loop g ∙ loop h
  squash : (x y : EMSpace1 G) → (p q : x ≡ y) → (r s : p ≡ q) → r ≡ s

EMSpace1Pointed : ∀ {ℓ} (G : Group {ℓ}) → Pointed {ℓ}
EMSpace1Pointed G = EMSpace1 G , base

