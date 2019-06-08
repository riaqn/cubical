{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Group.Properties where

open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Data.Group.Base

import Cubical.Foundations.Univalence as U
import Cubical.Foundations.HLevels as H
import Cubical.Core.Glue as G

open import Cubical.Data.Prod

open Group
open isGroup

private
  variable
    ℓ ℓ' : Level
    G : Group {ℓ}
    H : Group {ℓ'}
    f : morph G H

lCancel2 : {g0 g1 : G .type} (g' : G .type) → (G .groupStruc .comp g' g0 ≡ G .groupStruc .comp g' g1) → g0 ≡ g1
lCancel2 {G = group G Gset (group-struct id inv comp lUnit rUnit assoc lCancel rCalcel)} {g0 = g0} {g1 = g1} g' p =
  g0 ≡⟨  sym (lUnit _ ) ⟩
  comp id g0 ≡⟨ cong (λ x → comp x g0) (sym (lCancel _)) ⟩
  comp (comp (inv g') g') g0 ≡⟨ assoc _ _ _ ⟩
  comp (inv g') (comp g' g0) ≡⟨ cong (comp (inv g')) p ⟩
  comp (inv g') (comp g' g1) ≡⟨ sym (assoc _ _ _) ⟩
  comp (comp (inv g') g') g1 ≡⟨ cong (λ x → comp x g1) (lCancel _) ⟩
  comp id g1 ≡⟨ lUnit _ ⟩
  g1 ∎

isInvOf : (g0 g1 : G .type) → Type _
isInvOf {G = group G Gset (group-struct id _ comp _ _ _ _ _)} g0 g1 = (comp g0 g1 ≡ id) ×Σ (comp g1 g0 ≡ id)

unique-inv : {g0 g1 : G .type} (g : G .type) → 
             (isInvOf {G = G} g g0) → 
             (isInvOf {G = G} g g1) → 
             g0 ≡ g1
unique-inv {G = group G Gset (group-struct id inv comp lUnit rUnit assoc _ _) } {g0 = g0} {g1 = g1}  g  h0 h1 =
 g0 ≡⟨ sym (rUnit _) ⟩
 comp g0 id ≡⟨ cong (comp g0) (sym (h1 .fst)) ⟩
 comp g0 (comp g g1) ≡⟨ sym (assoc _ _ _) ⟩
 comp (comp g0 g) g1 ≡⟨ cong (λ x → comp x g1) (h0 .snd) ⟩
 comp id g1 ≡⟨ lUnit _ ⟩
 g1 ∎

morph-id : (f : morph G H) → f .fst (G .groupStruc .id) ≡ H .groupStruc .id
morph-id {G = G} {H = H} (f , fmorph) =
         lCancel2 {G = H}(f (G .groupStruc .id)) (helper G H (f , fmorph))
           where
             helper : (G : Group {ℓ}) → (H : Group {ℓ'}) → (f : morph G H) → H .groupStruc .comp (f .fst (G .groupStruc .id))
                      (f .fst (G .groupStruc .id))
                      ≡ H .groupStruc .comp (f .fst (G .groupStruc .id)) (H .groupStruc .id)
             helper (group G _  (group-struct Gid _ Gcomp GlUnit _ _ _ _))
                    (group H _ (group-struct Hid _ Hcomp _ HrUnit _ _ _)) (f , fmorph) = 
               Hcomp (f Gid) (f Gid) ≡⟨ sym (fmorph _ _) ⟩
               f (Gcomp Gid Gid) ≡⟨ cong f (GlUnit _) ⟩
               f Gid ≡⟨ sym (HrUnit _) ⟩
               Hcomp (f Gid) Hid ∎

morph-inv' : {G : Group {ℓ}} {H : Group {ℓ'}} {f : morph G H} (g : G .type) → isInvOf {G = H} (f .fst g) (f .fst (G .groupStruc .inv g))
morph-inv' {G = group G Gset (group-struct Gid Ginv Gcomp GlUnit GrUnit Gassoc GlCancel GrCancel)}
           {H = group H Hset (group-struct Hid Hinv Hcomp HlUnit HrUnit Hassoc HlCancel HrCancel)}
           {f = (f , fmorph)} g =
  (Hcomp (f g) (f (Ginv g)) ≡⟨ sym (fmorph _ _) ⟩
  f (Gcomp g (Ginv g)) ≡⟨ cong f (GrCancel _) ⟩
  f (Gid) ≡⟨ morph-id {G = G_} {H = H_} (f , fmorph) ⟩
  Hid ∎  ) ,
  (Hcomp (f (Ginv g)) (f g) ≡⟨ sym (fmorph _ _) ⟩
  f (Gcomp (Ginv g) g) ≡⟨ cong f (GlCancel _) ⟩
  f (Gid) ≡⟨ morph-id {G = G_} {H = H_} (f , fmorph) ⟩
  Hid ∎   )
    where
      G_ = group G Gset (group-struct Gid Ginv Gcomp GlUnit GrUnit Gassoc GlCancel GrCancel)
      H_ = group H Hset (group-struct Hid Hinv Hcomp HlUnit HrUnit Hassoc HlCancel HrCancel)

morph-inv : (f : morph G H) → (g : G .type) → f .fst (G .groupStruc .inv g) ≡ H .groupStruc .inv (f .fst g)
morph-inv {G = G} {H = H} (f , fmorph) g = unique-inv {G = H} (f g) (morph-inv' {G = G} {H = H} {f = f , fmorph} g)  (H .groupStruc .rCancel _ , H .groupStruc .lCancel _)

ua : ∀ {ℓ} {G H : Group {ℓ}} → G ≃ H  → G ≡ H
ua {G = group G Gset Ggroup} {H = group H Hset Hgroup} ((f , fmorph) , fequiv) i = group (p i) (p-set i) (p-group i)
  where
    G_ : Group 
    G_ = group G Gset Ggroup

    H_ : Group 
    H_ = group H Hset Hgroup

    p : G ≡ H
    p = U.ua (f , fequiv)

    p-set : PathP (λ i → isSet (p i)) Gset Hset
    p-set = isProp→PathP {B = isSet} (λ x → H.isPropIsOfHLevel 2 x) p Gset Hset

    p-group : PathP (λ i → isGroup (p i)) Ggroup Hgroup
    p-group i = group-struct ( p-id i) {!!} {!!} {!!} {!!} {!!} {!!} {!!}
      where
      q : G ≡ p i
      q j = p (i ∧ j)

      p-id : PathP (λ i → p i) (Ggroup .id) (Hgroup .id)
      p-id i = G.glue (λ  { (i = i0) → Ggroup .id
                          ; (i = i1) → Hgroup .id }) (morph-id {G = G_} {H = H_} (f , fmorph) i)

      p-inv : PathP (λ i →  p i → p i) (Ggroup .inv) (Hgroup .inv)
      p-inv i g = G.glue (λ { (i = i0) → Ggroup .inv g
                             ; (i = i1) → Hgroup .inv g}) {!morph-inv (f , fmorph) (G.unglue (~ i ∨ i) g) i!}

