{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.EMSpace.Properties where

open import Cubical.HITs.EMSpace.Base
open import Cubical.Data.HomotopyGroup.Base
open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Data.Group as G using (Group; isGroup; group; group-struct) 
open import Cubical.Foundations.HLevels
open import Cubical.Core.Glue
import Cubical.Foundations.Univalence as U
open import Cubical.Foundations.Transport
open import Cubical.HITs.Truncation renaming (ind to tind)
open import Cubical.Data.Sigma hiding (comp)

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
      (Bloop-comp : (g h : G .type) → PathP (λ i → PathP (λ j → B (loop-comp g h i j)) Bbase (Bloop h i)) (Bloop g) (Bloop (G .groupStruc .comp g h)))
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

ind' : {B : (EMSpace1 G) → Set ℓ'}
      (Bbase : B base)
      (Bloop : (g : G .type) → PathP (λ i → B (loop g i)) Bbase Bbase)
      (Bsquash : (x : EMSpace1 G) → isOfHLevel 2 (B x))
      (x : EMSpace1 G) →
      B x
ind' {G = G} {B = B} Bbase Bloop Bsquash x = ind {B = B} Bbase Bloop Bloop-id  Bloop-comp (λ y → hLevelLift {n = 2} 1 (Bsquash y) ) x
  where
  -- TODO: prove transp≃PathP so I don't have to use J explicitly
    lemma : ∀ {ℓ} {B : I → Type ℓ} → ((i : I) → isProp (B i)) → {b0 : B i0} {b1 : B i1} → PathP (λ i → B i) b0 b1
    lemma hB = toPathP (hB _ _ _)

    Bloop-id : PathP (λ i → PathP (λ j → B (loop-id i j)) Bbase Bbase)
               (Bloop (G .groupStruc .id)) refl
    Bloop-id = (lemma λ i → J (λ b p → ∀ bb → isProp (PathP (λ j → B (p j)) Bbase bb)) (Bsquash _ _) (loop-id i) Bbase)

    Bloop-comp : (g h : G .type) →
      PathP (λ i → PathP (λ j → B (loop-comp g h i j)) Bbase (Bloop h i))
      (Bloop g) (Bloop (G .groupStruc .comp g h))
    Bloop-comp g h = lemma (λ i → J (λ b p → ∀ bb → isProp (PathP (λ j → B (p j)) Bbase bb)) (Bsquash _ _) (loop-comp g h i) (Bloop h i))

-- lemma 8.9.1 in hott book
code-loop : {A : Set ℓ} {a0 : A}
            {code : A → Set ℓ'}
            (c0 : code a0)
            (decode : {a : A} → code a → a0 ≡ a) → 
            ((c : code a0) → transport (cong code (decode c)) c0 ≡ c) → 
            (decode c0 ≡ refl) → 
            code a0 ≃ (a0 ≡ a0)
code-loop {A = A} {a0} {code} c0 decode encode-decode decode-encode' = E.isoToEquiv (I.iso decode encode decode-encode encode-decode)
  where
    encode : {a : A} → (a0 ≡ a) → code a
    encode p = transport (cong code p) c0

    decode-encode : ∀ p → decode (encode p) ≡ p
    decode-encode p = J (λ a p → decode (encode p) ≡ p)
      (decode (encode refl) ≡⟨ cong decode (transportRefl c0) ⟩
       decode c0 ≡⟨ decode-encode' ⟩
       refl ∎
      ) p

some-result : ((π^ 0) (EMSpace1Pointed G)) ≡ G
some-result {ℓ} {G = G} = p0 ∙ (sym p1)
  where
  e' : G .type ≃ (Ω^-group 0 (EMSpace1Pointed G) squash) .type
  e' = code-loop {code = λ x → codes x .fst } (G .groupStruc .id) decode encode-decode loop-id
    where
    module Codes where
      record Struc {ℓ'} (A : Type ℓ') (a-id : A) (a-comp : A → A → A) : Type (ℓ-max ℓ ℓ') where
        coinductive
        constructor struc
        field
          f : G .type → A
          f-id : f (G .groupStruc .id) ≡ a-id
          f-comp : (g0 g1 : G .type) → f (G .groupStruc .comp g0 g1) ≡ a-comp (f g0) (f g1)

      struc0 : Struc (G .type ≡ G .type) refl _∙_
      struc0 = struc f f-id f-comp
        where
          f' : G .type → G .type ≃ G .type
          f' g = helper G g
            where
            helper : ∀ {ℓ} (G : Group {ℓ}) → G .type → G .type ≃ G .type
            helper (group G Gset (group-struct id inv comp lUnit rUnit assoc lCancel rCancel)) g =
                   E.isoToEquiv (I.iso pos neg pos-neg neg-pos)
              where
              pos : G → G
              pos g' = comp g' g

              neg : G → G
              neg g' = comp g' (inv g)

              pos-neg : ∀ g' → pos (neg g') ≡ g'
              pos-neg g' = comp (comp g' (inv g)) g ≡⟨ assoc _ _ _ ⟩
                           comp g' (comp (inv g) g) ≡⟨ cong (comp g') (lCancel _) ⟩
                           comp g' id ≡⟨ rUnit _ ⟩
                           g' ∎

              neg-pos : ∀ g' → neg (pos g') ≡ g'
              neg-pos g' = comp (comp g' g) (inv g) ≡⟨ assoc _ _ _ ⟩
                           comp g' (comp g (inv g)) ≡⟨ cong (comp g') (rCancel _) ⟩
                           comp g' id ≡⟨ rUnit _ ⟩
                           g' ∎


          f : G .type → G .type ≡ G .type
          f g = U.ua (f' g)

          f-id : f (G .groupStruc .id) ≡ refl
          f-id = subst (λ x → U.ua x ≡ refl) (sym helper) U.uaIdEquiv
            where
            helper : f' (G .groupStruc .id) ≡ E.idEquiv _
            helper = E.equivEq _ _ (funExt (λ g → G .groupStruc .rUnit _))

          f-comp : (g0 g1 : G .type) →
                   f  (G .groupStruc .comp g0 g1) ≡ f g0 ∙ f g1
          f-comp g0 g1 = subst (λ x → U.ua x ≡ f g0 ∙ f g1) (sym helper) (U.uaCompEquiv _ _)
            where
            helper : f' (G .groupStruc .comp g0 g1) ≡ E.compEquiv (f' g0) (f' g1)
            helper = E.equivEq _ _ (funExt (λ g → sym (G .groupStruc .assoc _ _ _)))

      G' : Σ (Type ℓ) isSet
      G' = G .type , G .setStruc

      e : (G .type ≡ G .type) ≃ (G' ≡ G')
      e = (HLevel≃ {n = 2} {A = G .type} {B = G .type} {hA = G .setStruc} {hB = G .setStruc})

      struc1 : Struc (G' ≡ G') refl _∙_
      struc1 = transport (sym q) struc0
        where
          q : Struc (G' ≡ G') refl _∙_ ≡ Struc (G .type ≡ G .type) refl _∙_ 
          q i = Struc (p i) (p-id i) (p-comp i)
            where
              p : (G' ≡ G') ≡ (G .type ≡ G .type)
              p = U.ua (E.invEquiv e)

              p-id : PathP (λ i → p i) refl refl
              p-id i = glue (λ { (i = i0) → refl ; (i = i1) → refl }) refl

              p-comp : PathP (λ i → p i → p i → p i) _∙_ _∙_
              p-comp i g0 g1 = glue (λ { (i = i0) → g0 ∙ g1 ; (i = i1) → g0 ∙ g1 })
                                    ((unglue (i ∨ ~ i) g0) ∙ (unglue (i ∨ ~ i) g1))

      Gloop = Struc.f struc1
      Gloop-id = Struc.f-id struc1

      Gloop-comp : (g h : G .type) → PathP (λ i → (G .type , G .setStruc) ≡ Gloop h i) (Gloop g) (Gloop (G .groupStruc .comp g h))
      Gloop-comp g h i j =  hcomp (λ k → λ { (i = i0) → Gloop g j
                                             ; (i = i1) → (Struc.f-comp struc1) g h (~ k) j
                                             ; (j = i0) → (G .type , G .setStruc)
                                             ; (j = i1) → Gloop h i
                                             }) (compPath-filler (Gloop g) (Gloop h) i j)

      codes : EMSpace1 G → HLevel 2
      codes = ind (G .type , G .setStruc) Gloop Gloop-id Gloop-comp (λ _ → hLevelHLevelSuc 1)

    codes = Codes.codes
    

    decode : {a : EMSpace1 G} → codes a .fst → base ≡ a
    decode {a = a} = ind' {B = λ a → codes a .fst → base ≡ a } loop loop-loop (λ x → hLevelPi 2 (λ _ → squash _ _)) a
      where
      loop-loop : (g : G .type) →
        PathP (λ i → codes (loop {G = G} g i) .fst → base {G = G} ≡ loop g i) loop loop
      loop-loop g i x j = hcomp (λ k → λ { (i = i0) → loop-comp x g (~ k) j
                                          ; (i = i1) → loop x j
                                          ; (j = i0) → base
                                          ; (j = i1) → loop g (i ∨ ~ k) })
                                (loop helper j)
                          where
                            q : hcomp (λ k → λ { (i = i0) → G .type ; (i = i1) → G .type}) (Codes.Struc.f Codes.struc0 (transport refl g) i) ≡
                                (Codes.Struc.f Codes.struc0 (transport refl g) i)
                            q k = hfill (λ k → λ { (i = i0) → G .type
                                                  ; (i = i1) → G .type}) (inS (Codes.Struc.f Codes.struc0 (transport refl g) i)) (~ k)
                            x' : (Codes.Struc.f Codes.struc0 (transport refl g) i)
                            x' = transport q x

                            helper = hcomp (λ k → λ { (i = i0) → G .groupStruc .comp (transportRefl x k) (transportRefl g k)
                                                    ; (i = i1) → transportRefl x k
                                                    }) (unglue (i ∨ ~ i) x')

    encode-decode : (c : codes (snd (iterate 0 Ω (EMSpace1Pointed G))) .fst) →
                  transport (cong (λ x → codes x .fst) (decode {a = base} c))
                  (G .groupStruc .id)
                  ≡ c
    encode-decode c =
      transport refl (transport refl (G .groupStruc .comp (transport refl (G .groupStruc .id)) (transport refl c))) ≡⟨ transportRefl _  ⟩
      transport refl (G .groupStruc .comp (transport refl (G .groupStruc .id)) (transport refl c)) ≡⟨ transportRefl _  ⟩
      G .groupStruc .comp (transport refl (G .groupStruc .id)) (transport refl c) ≡⟨ cong (λ x → G .groupStruc .comp x (transport refl c)) (transportRefl _) ⟩
      G .groupStruc .comp (G .groupStruc .id) (transport refl c) ≡⟨ cong (G .groupStruc .comp (G .groupStruc .id)) (transportRefl _) ⟩
      G .groupStruc .comp (G .groupStruc .id) c ≡⟨ G .groupStruc .lUnit c ⟩
      c ∎

  p0 : (π^ 0 (EMSpace1Pointed G)) ≡ Ω^-group 0 (EMSpace1Pointed G) squash
  p0 = π^≡Ω^-group {k = 0} (EMSpace1Pointed G) squash

  p1 : G ≡ Ω^-group 0 (EMSpace1Pointed G) squash
  p1 = G.ua (e' , λ g0 g1 i j → hcomp
                                             (λ k → λ { (i = i0) → loop-comp g0 g1 k j
                                                      ; (i = i1) → compPath-filler (loop g0) (loop g1) k j
                                                      ; (j = i0) → base
                                                      ; (j = i1) → loop g1 k })
                                             (loop g0 j) )
