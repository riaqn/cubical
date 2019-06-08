
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.EMSpace.Properties where

open import Cubical.HITs.EMSpace.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Data.Group as G using (Group; isGroup; group; group-struct) 
open import Cubical.Foundations.HLevels
open import Cubical.Core.Glue
open import Cubical.Foundations.Univalence using (ua; uaIdEquiv; uaCompEquiv)
open import Cubical.Foundations.Transport
open import Cubical.HITs.Truncation renaming (ind to tind) 

import Cubical.Foundations.HAEquiv as HAE
import Cubical.Foundations.Isomorphism as I
import Cubical.Foundations.Equiv as E

private
  variable
    ℓ ℓ' : Level
    G : Group {ℓ}

open Group
open isGroup

ind : {B : (EMSpace1 G) → Set ℓ'}
      (Bbase : B base)
      (Bloop : (g : G .type) → PathP (λ i → B (loop g i)) Bbase Bbase)
      (Bloop-id : PathP (λ i → PathP (λ j → B (loop-id i j)) Bbase Bbase) (Bloop (G .groupStruc .id)) refl)
      (Bloop-comp : (g h : G .type) → PathP (λ i → PathP (λ j → B (loop-comp g h i j)) Bbase (Bloop h i)) (Bloop g) (Bloop (G .groupStruc .comp h g)))
      (Bsquash : (x : EMSpace1 G) → isOfHLevel 3 (B x))
      (x : EMSpace1 G) →
      B x
ind Bbase _ _ _ _ base = Bbase
ind _ Bloop _ _ _ (loop g i) = Bloop g i
ind _ _ Bloop-id _ _ (loop-id i j) = Bloop-id i j
ind _ _ _ Bloop-comp _ (loop-comp g h i j) = Bloop-comp g h i j
ind {G = G} {B = B} Bbase Bloop Bloop-id Bloop-comp Bsquash (squash x y p q r s i j k) = Bsquash' x y p q r s i j k
  where
    ind' : (x : EMSpace1 G) → B x
    ind' = ind Bbase Bloop Bloop-id Bloop-comp Bsquash

    Bsquash' : (x y : EMSpace1 G) (p q : x ≡ y) (r s : p ≡ q) → PathP (λ i → PathP (λ j → PathP (λ k → B (squash x y p q r s i j k)) (ind' x) (ind' y)) (cong ind' p) (cong ind' q)) (cong (cong ind') r) (cong (cong ind') s)
    Bsquash' x y p q r s = isOfHLevel→isOfHLevelDep {n = 3} Bsquash (ind' x) (ind' y) (cong ind' p) (cong ind' q) (cong (cong ind') r) (cong (cong ind') s) (squash x y p q r s)

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
some-result {ℓ} {G = group G Gset (isGroup.group-struct id inv _⊙_ lUnit rUnit assoc lCancel rCancel)} = G.compIso {!!} {!!}
  where

  G_ : Group {ℓ}
  G_ = group G Gset (isGroup.group-struct id inv _⊙_ lUnit rUnit assoc lCancel rCancel)

  e' = code-loop {code = λ x → codes x .fst } id decode (λ c → (transportRefl (c ⊙ id)) ∙ (rUnit c)) loop-id
    where

    codes : EMSpace1 G_ → HLevel 2
    codes = ind (G , Gset) Gloop {!Gloop-id!} {!!} (λ _ → hLevelHLevelSuc 1)
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
                         (inv g ⊙ g) ⊙ a ≡⟨ cong (λ x → x ⊙ a) (lCancel _) ⟩ id ⊙ a ≡⟨ lUnit _ ⟩
                         a ∎

        Gloop'-id : Gloop' id ≡ E.idEquiv G
        Gloop'-id = E.equivEq (Gloop' id) (E.idEquiv G) (funExt (λ x → lUnit x))

        eq : ((G , Gset)  ≡ (G , Gset)) ≡ (G ≡ G)
        eq = ua (E.invEquiv (HLevel≃ {n = 2} {A = G} {B = G} {hA = Gset} {hB = Gset}))

        Gloop : G → (G , Gset) ≡ (G , Gset)
        Gloop g = (HLevel≃ {n = 2}) .fst (ua (Gloop' g))

        Gloop-id : Gloop id ≡ refl {x = (G , Gset)}
        Gloop-id = {!!}

        -- E.invEq (HAE.congEquiv (E.invEquiv (HLevel≃ {n = 2}))) {!!}
        -- (subst (λ e → ua e ≡ refl) (sym Gloop'-id) uaIdEquiv)

        Gloop'-comp : (g h : G) → Gloop' (h ⊙ g) ≡ E.compEquiv (Gloop' g) (Gloop' h)
        Gloop'-comp g h = E.equivEq _ _ (funExt (λ x → assoc _ _ _))

        Gloop-comp : (g h : G) → Gloop (h ⊙ g) ≡ Gloop g ∙ Gloop h
        Gloop-comp g h = E.invEq (HAE.congEquiv (E.invEquiv (HLevel≃ {n = 2})))
                         (ua (Gloop' (h ⊙ g)) ≡⟨ cong ua (Gloop'-comp _ _) ⟩
                          ua (E.compEquiv (Gloop' g) (Gloop' h)) ≡⟨ uaCompEquiv _ _ ⟩
                          (ua (Gloop' g)) ∙ (ua (Gloop' h)) ∎ )

        Gloop-comp' : (g h : G) → PathP (λ i → (G , Gset) ≡ Gloop h i) (Gloop g) (Gloop (h ⊙ g))
        Gloop-comp' g h i j =  hcomp (λ k → λ { (i = i0) → Gloop g j
                                               ; (i = i1) → Gloop-comp g h (~ k) j
                                               ; (j = i0) → (G , Gset)
                                               ; (j = i1) → Gloop h i
                                               }) (compPath-filler (Gloop g) (Gloop h) i j)

    decode : {a : EMSpace1 G_} → codes a .fst → base ≡ a
    decode {a = a} = {!!}
      where
        loop-loop : (g : G) →
          PathP (λ i → codes (loop g i) .fst → base ≡ loop g i) loop loop
        loop-loop g = {!!}

  p : (∥ base ≡ base ∥ 2) ≡ (base ≡ base)
  p = ua (idemTrunc (squash _ _))

  G' : Group
  G' = G.transportGroup (π^ 0 (EMSpace1Pointed G_)) p

  EM≃G' : G.Iso ((π^ 0) (EMSpace1Pointed G_)) G'
  EM≃G' = G.transportIso p

  -- G'≃G : G.Iso G' G_
  -- G'≃G = ?
