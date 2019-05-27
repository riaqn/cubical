
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.EMSpace.Properties where

open import Cubical.HITs.EMSpace.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Group as G using (Group; group ; isGroup)
open import Cubical.Core.Prelude hiding (comp)
open import Cubical.HITs.SetTruncation
open import Cubical.Core.Glue
open import Cubical.Data.Sigma
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels

import Cubical.Foundations.HAEquiv as HAE
import Cubical.Foundations.Isomorphism as I
import Cubical.Foundations.Equiv as E


private
  variable
    ℓ ℓ' : Level
    G : Group {ℓ}

open Group
open isGroup

lemma : ∀ {A : Set ℓ} {B : Set ℓ'} (f : A → B)
        {x y z : A}
        (p : x ≡ y)
        (q : y ≡ z) → 
        cong f (p ∙ q) ≡ (cong f p) ∙ (cong f q)
lemma f {x} {y} {z} p q i j = hcomp (λ k → λ { (i = i0) → f (compPath-filler p q k j)
                                        ; (i = i1) → compPath-filler (cong f p) (cong f q) k j
                                        ; (j = i0) → f x
                                        ; (j = i1) → f (q k)})
                               (f (p j))

ind : {B : Set ℓ'}
       (Bbase : B)
      (Bloop : (g : G .type) → Bbase ≡ Bbase)
      (Bloop-id : Bloop (G .groupStruc .id) ≡ refl)
      (Bloop-comp : (g h : G .type) → Bloop (G .groupStruc .comp g h) ≡ (Bloop g) ∙ (Bloop h))
      (Bsquash : isOfHLevel 3 B )
      (x : EMSpace1 G) →
      B
ind Bbase _ _ _ _ base = Bbase
ind _ Bloop _ _ _ (loop g i) = Bloop g i
ind _ _ Bloop-id _ _ (loop-id i j) = Bloop-id i j

ind {G = G} {B = B} Bbase Bloop Bloop-id Bloop-comp Bsquash (loop-comp g h i j) = ((Bloop-comp g h) ∙ sym (lemma ind' (loop g) (loop h))) i j
  where
    ind' : (x : EMSpace1 G) → B
    ind' = ind Bbase Bloop Bloop-id Bloop-comp Bsquash

ind {G = G} {B = B} Bbase Bloop Bloop-id Bloop-comp Bsquash (squash x y p q r s i j k) =
  Bsquash x' y' p' q' r' s' i j k
  where
    ind' : (x : EMSpace1 G) → B
    ind' = ind Bbase Bloop Bloop-id Bloop-comp Bsquash

    x' : B
    x' = ind' x

    y' : B
    y' = ind' y

    p' : x' ≡ y'
    p' = cong ind' p

    q' : x' ≡ y'
    q' = cong ind' q

    r' : p' ≡ q'
    r' = cong (cong ind') r

    s' : p' ≡ q'
    s' = cong (cong ind') s

-- lemma 8.9.1 in hott book
code-loop : {A : Set ℓ} {a0 : A}
            {code : A → Set ℓ'}
            (c0 : code a0)
            (decode : {a : A} → code a → a0 ≡ a) → 
            ((c : code a0) → transport (cong code (decode c)) c0 ≡ c) → 
            (decode c0 ≡ refl) → 
            (a0 ≡ a0) ≃ code a0
code-loop {A = A} {a0} {code} c0 decode encode-decode decode-encode' = E.isoToEquiv (I.iso encode decode encode-decode decode-encode)
  where
    encode : {a : A} → (a0 ≡ a) → code a
    encode p = transport (cong code p) c0

    decode-encode : ∀ p → decode (encode p) ≡ p
    decode-encode p = J (λ a p → decode (encode p) ≡ p)
      (decode (encode refl) ≡⟨ cong decode (transportRefl c0) ⟩
       decode c0 ≡⟨ decode-encode' ⟩
       refl ∎
      ) p

some-result : G.Iso ((π^ 0) (EMSpace1Pointed G)) G
some-result {ℓ} {G = group G Gset (isGroup.group-struct id inv _⊙_ lUnit rUnit assoc lCancel rCancel)} = G.Iso'→Iso (G.iso' (E.equivToIso e) {!!})
  where

  G_ : Group {ℓ}
  G_ = group G Gset (isGroup.group-struct id inv _⊙_ lUnit rUnit assoc lCancel rCancel)

  e' : (base ≡ base) ≃ G
  e' = code-loop {code = λ x → codes x .fst } {!!} {!!} {!!} {!!}
    where
    codes : EMSpace1 G_ → HLevel 2
    codes = ind (G , Gset) Gloop {!!} {!!} (hLevelHLevelSuc 1)
      where
        Gloop' : G → G ≃ G
        Gloop' g = (E.isoToEquiv (I.iso (_⊙_ g) (_⊙_ (inv g)) rightInv leftInv))
          where
            rightInv : (b : G) → g ⊙ ((inv g) ⊙ b) ≡ b
            rightInv b = g ⊙ (inv g ⊙ b) ≡⟨ sym (assoc _ _ _) ⟩
                          (g ⊙ inv g) ⊙ b ≡⟨ cong (λ x → x ⊙ b) (rCancel _) ⟩
                          id ⊙ b ≡⟨ lUnit _ ⟩
                          b ∎

            leftInv : (a : G) → (inv g ⊙ (g ⊙ a)) ≡ a
            leftInv a = inv g ⊙ (g ⊙ a) ≡⟨ sym (assoc _ _ _) ⟩
                         (inv g ⊙ g) ⊙ a ≡⟨ cong (λ x → x ⊙ a) (lCancel _) ⟩
                         id ⊙ a ≡⟨ lUnit _ ⟩
                         a ∎

        Gloop : G → (G , Gset) ≡ (G , Gset)
        Gloop g = transport (HLevel≡ {n = 2}) (ua (Gloop' g))

        Gloop-e : Gloop id ≡ refl
        Gloop-e = E.invEq (HAE.congEquiv ((transport eq) , (isEquivTransport eq))) Gloop-e'
          where
             eq : ((G , Gset)  ≡ (G , Gset)) ≡ (G ≡ G)
             eq = ua (E.invEquiv HLevel≃ {n = 2} {A = G} {B = G} {hA = Gset} {hB = Gset})

             Gloop-e' : transport eq (Gloop id) ≡ transport eq refl
             Gloop-e' = transport eq (Gloop id) ≡⟨ transportTransport⁻ eq (ua (Gloop' id)) ⟩
                       ua (Gloop' id) ≡⟨ cong ua (E.equivEq (Gloop' id) (idEquiv G) (funExt (λ x → lUnit _)) ) ⟩
                       ua (idEquiv G) ≡⟨ uaIdEquiv ⟩
                       refl ≡⟨ {!!} ⟩
                       transport eq refl ∎

        Gloop-comp : (g h : G) → Gloop (g ⊙ h) ≡ Gloop g ∙ Gloop h
        Gloop-comp g h = {!!}

  --   encode : (x : EMSpace1 G_) → base ≡ x → (codes x .fst)
  --   encode = {!!}

  -- e : ∥ base ≡ base ∥₀ ≃ G
  e = E.compEquiv (idemSetTrunc (squash _ _)) e'
