module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.Involution.Core.Action

/-!
# Explicit fusion in the ternary involution centralizer

Every nonidentity involution of the actual centralizer of `involution` is
conjugate to `involution` by an octonion automorphism. The 24 long-root words
and 24 short-root/torus words exhaust the centralizer: their distinct images
of the three algebra generators, together with the proved frame bound, give
surjectivity. For each involutive word, a finite coordinate calculation gives
a local conjugator to one of three representatives. Explicit root/Weyl words
fuse those representatives. All finite identities are checked by the kernel;
the lookup table supplies witnesses, not an assumed classification.

The normal forms repeat the private enumerators in `Involution.Order`, with
coordinate action formulas from `Involution.Core.Action`, so that the shared
modules and their public boundaries need no changes.

Application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Main Theorem 0.1.2(4), printed pp.3–4, repeated on pp.481–482. The local
configuration I.4(G1), p.417, is a recognition hypothesis, not a coverage
result. Coordinate conventions and automorphisms are from the licensed ATLAS
port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.TernaryLocals.CharacterGeometry.InvolutionConjugacy
open Atlas.SplitOctonion Involution Involution.CoreCalculation
set_option maxRecDepth 100000
private def longWord (i : Fin 24) : P :=
  quaternionI false ^ (i.val / 6) * quaternionJ false ^ (i.val / 3 % 2) *
    positive false ^ (i.val % 3)
private def shortWord (i : Fin 24) : P :=
  quaternionI true ^ (i.val / 12) * quaternionJ true ^ (i.val / 6 % 2) *
    positive true ^ (i.val / 2 % 3) * torusActor ^ (i.val % 2)
private def word (p : Fin 24 × Fin 24) : P := shortWord p.2 * longWord p.1
private def longApply (i : Fin 24) (x : Carrier K) : Carrier K :=
  (qiApply false)^[i.val / 6] ((qjApply false)^[i.val / 3 % 2]
    ((genApply 0)^[i.val % 3] x))
private def shortApply (i : Fin 24) (x : Carrier K) : Carrier K :=
  (qiApply true)^[i.val / 12] ((qjApply true)^[i.val / 6 % 2]
    ((genApply 2)^[i.val / 2 % 3] ((genApply 4)^[i.val % 2] x)))
private def wordApply (p : Fin 24 × Fin 24) (x : Carrier K) : Carrier K :=
  shortApply p.2 (longApply p.1 x)
private theorem pow_apply (g : P) (f : Carrier K → Carrier K)
    (h : ∀ x, g.val.val x = f x) (n : ℕ) (x : Carrier K) :
    (g^n).val.val x = f^[n] x := by
  change (g.val.val ^ n) x = _
  rw [LinearEquiv.pow_apply]
  exact congrFun (congrArg (fun f : Carrier K → Carrier K => f^[n]) (funext h)) x
private theorem long_apply (i : Fin 24) (x : Carrier K) :
    (longWord i).val.val x = longApply i x := by
  change (quaternionI false ^ _).val.val
    ((quaternionJ false ^ _).val.val ((positive false ^ _).val.val x)) = _
  rw [pow_apply _ _ (qi_apply false), pow_apply _ _ (qj_apply false),
    pow_apply (positive false) _ (gen_apply 0)]
  rfl
private theorem short_apply (i : Fin 24) (x : Carrier K) :
    (shortWord i).val.val x = shortApply i x := by
  change (quaternionI true ^ _).val.val
    ((quaternionJ true ^ _).val.val ((positive true ^ _).val.val
      ((torusActor ^ _).val.val x))) = _
  rw [pow_apply _ _ (qi_apply true), pow_apply _ _ (qj_apply true),
    pow_apply (positive true) _ (gen_apply 2), pow_apply torusActor _ (gen_apply 4)]
  rfl
private theorem word_apply (p : Fin 24 × Fin 24) (x : Carrier K) :
    (word p).val.val x = wordApply p x := by
  change (shortWord p.2).val.val ((longWord p.1).val.val x) = _
  rw [short_apply, long_apply]
  rfl
private theorem longWord_u (i : Fin 24) : (longWord i).val.val u = u := by
  rw [long_apply]
  exact (by decide +kernel : ∀ i : Fin 24, longApply i u = u) i
private theorem longWord_v (i : Fin 24) : (longWord i).val.val v = v := by
  rw [long_apply]
  exact (by decide +kernel : ∀ i : Fin 24, longApply i v = v) i
private theorem longWord_odd_injective :
    Function.Injective (fun i : Fin 24 => oddCoordinates ((longWord i).val.val w)) := by
  simp only [long_apply]
  decide +kernel
private theorem shortWord_fixed_injective :
    Function.Injective (fun i : Fin 24 =>
      (fixedCoordinates ((shortWord i).val.val u),
        fixedCoordinates ((shortWord i).val.val v))) := by
  simp only [short_apply]
  decide +kernel
private theorem word_injective : Function.Injective word := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hu := congrArg (fun g : P => g.val.val u) h
  have hv := congrArg (fun g : P => g.val.val v) h
  change (shortWord b).val.val ((longWord a).val.val u) =
    (shortWord d).val.val ((longWord c).val.val u) at hu
  change (shortWord b).val.val ((longWord a).val.val v) =
    (shortWord d).val.val ((longWord c).val.val v) at hv
  rw [longWord_u, longWord_u] at hu
  rw [longWord_v, longWord_v] at hv
  have hbd : b = d := shortWord_fixed_injective
    (Prod.ext (congrArg fixedCoordinates hu) (congrArg fixedCoordinates hv))
  subst d
  have he : longWord a = longWord c := mul_left_cancel h
  have hac : a = c := longWord_odd_injective
    (congrArg (fun g : P => oddCoordinates (g.val.val w)) he)
  exact Prod.ext hac rfl
private theorem word_surjective : Function.Surjective word := by
  apply ((Nat.bijective_iff_injective_and_card word).mpr ⟨word_injective, ?_⟩).2
  apply le_antisymm
  · exact Nat.card_le_card_of_injective word word_injective
  · simpa using Involution.card_le
private def representative : Fin 3 → Model K :=
  ![weylS,
    weylS * ambientGenerator 3 * ambientGenerator 1 * ambientGenerator 4 *
      ambientGenerator 2 * ambientGenerator 0 * weylR, 1]
private def representativeApply (c : Fin 3) (x : Carrier K) : Carrier K :=
  ![weylSApply x,
    weylSApply (genApply 3 (genApply 1 (genApply 4
      (genApply 2 (genApply 0 (weylRApply x)))))), x] c
private theorem representative_apply (c : Fin 3) (x : Carrier K) :
    (representative c).val x = representativeApply c x := by
  fin_cases c
  · rfl
  · change weylSApply ((generator 3).val.val ((generator 1).val.val
      ((generator 4).val.val ((generator 2).val.val
        ((generator 0).val.val (weylRApply x)))))) = _
    simp only [gen_apply]
    rfl
  · rfl

-- Each entry specifies a local conjugator and a representative. The list
-- is only witness data; the identity for every entry is checked below.
private def fusionData (p : Fin 24 × Fin 24) : (Fin 24 × Fin 24) × Fin 3 :=
  match p.1.val * 24 + p.2.val with
  | 1 => ((0, 0), 0)
  | 3 => ((0, 4), 0)
  | 5 => ((0, 2), 0)
  | 7 => ((0, 12), 0)
  | 17 => ((0, 8), 0)
  | 21 => ((0, 10), 0)
  | 25 => ((1, 0), 0)
  | 27 => ((1, 4), 0)
  | 29 => ((1, 2), 0)
  | 31 => ((1, 12), 0)
  | 41 => ((1, 8), 0)
  | 45 => ((1, 10), 0)
  | 49 => ((1, 1), 0)
  | 51 => ((1, 5), 0)
  | 53 => ((1, 3), 0)
  | 55 => ((1, 13), 0)
  | 65 => ((1, 9), 0)
  | 69 => ((1, 11), 0)
  | 73 => ((6, 1), 0)
  | 75 => ((6, 5), 0)
  | 77 => ((6, 3), 0)
  | 78 => ((0, 0), 1)
  | 79 => ((6, 13), 0)
  | 84 => ((0, 8), 1)
  | 89 => ((6, 9), 0)
  | 90 => ((0, 4), 1)
  | 93 => ((6, 11), 0)
  | 150 => ((1, 12), 1)
  | 156 => ((1, 2), 1)
  | 162 => ((1, 10), 1)
  | 193 => ((4, 1), 0)
  | 195 => ((4, 5), 0)
  | 197 => ((4, 3), 0)
  | 199 => ((4, 13), 0)
  | 209 => ((4, 9), 0)
  | 213 => ((4, 11), 0)
  | 222 => ((1, 1), 1)
  | 228 => ((1, 9), 1)
  | 234 => ((1, 5), 1)
  | 241 => ((4, 0), 0)
  | 243 => ((4, 4), 0)
  | 245 => ((4, 2), 0)
  | 247 => ((4, 12), 0)
  | 257 => ((4, 8), 0)
  | 261 => ((4, 10), 0)
  | 288 => ((0, 0), 2)
  | 289 => ((0, 6), 0)
  | 291 => ((0, 22), 0)
  | 293 => ((0, 14), 0)
  | 295 => ((0, 18), 0)
  | 305 => ((0, 20), 0)
  | 309 => ((0, 16), 0)
  | 313 => ((1, 6), 0)
  | 315 => ((1, 22), 0)
  | 317 => ((1, 14), 0)
  | 319 => ((1, 18), 0)
  | 329 => ((1, 20), 0)
  | 333 => ((1, 16), 0)
  | 337 => ((1, 7), 0)
  | 339 => ((1, 23), 0)
  | 341 => ((1, 15), 0)
  | 343 => ((1, 19), 0)
  | 353 => ((1, 21), 0)
  | 357 => ((1, 17), 0)
  | 361 => ((6, 0), 0)
  | 363 => ((6, 4), 0)
  | 365 => ((6, 2), 0)
  | 366 => ((0, 12), 1)
  | 367 => ((6, 12), 0)
  | 372 => ((0, 2), 1)
  | 377 => ((6, 8), 0)
  | 378 => ((0, 10), 1)
  | 381 => ((6, 10), 0)
  | 438 => ((1, 0), 1)
  | 444 => ((1, 8), 1)
  | 450 => ((1, 4), 1)
  | 481 => ((4, 7), 0)
  | 483 => ((4, 23), 0)
  | 485 => ((4, 15), 0)
  | 487 => ((4, 19), 0)
  | 497 => ((4, 21), 0)
  | 501 => ((4, 17), 0)
  | 510 => ((1, 13), 1)
  | 516 => ((1, 3), 1)
  | 522 => ((1, 11), 1)
  | 529 => ((4, 6), 0)
  | 531 => ((4, 22), 0)
  | 533 => ((4, 14), 0)
  | 535 => ((4, 18), 0)
  | 545 => ((4, 20), 0)
  | 549 => ((4, 16), 0)
  | _ => ((0, 0), 0)
private def conjugator (p : Fin 24 × Fin 24) : Model K :=
  (word (fusionData p).1).val * representative (fusionData p).2
private def signApply (x : Carrier K) : Carrier K :=
  ![-x 0,x 1,-x 2,x 3,x 4,-x 5,x 6,-x 7]

private def localRepresentative : Fin 3 → Fin 24 × Fin 24 := ![(0,1),(3,6),(12,0)]
private theorem representatives_fused : ∀ c k j,
    wordApply (localRepresentative c) (representativeApply c (marks k)) j =
      representativeApply c (signApply (marks k)) j := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem finite_fusion : ∀ p : Fin 24 × Fin 24,
    (∀ k j, wordApply p (wordApply p (marks k)) j = marks k j) →
    (∀ k j, wordApply p (marks k) j = marks k j) ∨
    (∀ k j, wordApply p (wordApply (fusionData p).1 (marks k)) j =
      wordApply (fusionData p).1 (wordApply (localRepresentative (fusionData p).2) (marks k)) j) := by
  rintro ⟨a,b⟩
  revert b
  fin_cases a <;> decide +kernel

/-- Every nonidentity involution in the displayed centralizer is conjugate
by an actual octonion automorphism to the marked torus involution. -/
theorem centralizer_involution_conjugate (x : P) (hx : x^2 = 1) (hne : x ≠ 1) :
    ∃ g : Model K, x.val = g * involution * g⁻¹ := by
  obtain ⟨p, rfl⟩ := word_surjective x
  have hs : ∀ k j, wordApply p (wordApply p (marks k)) j = marks k j := by
    intro k j
    have h := congrArg (fun g : P => g.val.val (marks k) j) hx
    change (word p).val.val ((word p).val.val (marks k)) j = marks k j at h
    simpa only [word_apply] using h
  rcases finite_fusion p hs with hi | hf
  · apply (hne ?_).elim
    apply local_ext
    intro k j
    change (word p).val.val (marks k) j = marks k j
    simpa only [word_apply] using hi k j
  have hl : (word p).val * (word (fusionData p).1).val =
      (word (fusionData p).1).val * (word (localRepresentative (fusionData p).2)).val := by
    have he : word p * word (fusionData p).1 =
        word (fusionData p).1 * word (localRepresentative (fusionData p).2) := by
      apply local_ext
      intro k j
      change (word p).val.val ((word (fusionData p).1).val.val (marks k)) j =
        (word (fusionData p).1).val.val
          ((word (localRepresentative (fusionData p).2)).val.val (marks k)) j
      simpa only [word_apply] using hf k j
    exact congrArg (fun g : P => g.val) he
  have hr (c : Fin 3) : (word (localRepresentative c)).val * representative c =
      representative c * involution := by
    have h (k : Fin 3) :
        (word (localRepresentative c)).val.val ((representative c).val (marks k)) =
          (representative c).val (involution.val (marks k)) := by
      apply funext
      intro j
      simpa only [word_apply, representative_apply, involution_apply, signApply] using
        representatives_fused c k j
    exact ext_generators _ _ (h 0) (h 1) (h 2)
  refine ⟨conjugator p, ?_⟩
  apply (eq_mul_inv_iff_mul_eq).mpr
  change (word p).val * ((word (fusionData p).1).val * representative (fusionData p).2) =
    ((word (fusionData p).1).val * representative (fusionData p).2) * involution
  rw [← _root_.mul_assoc, hl, _root_.mul_assoc, hr, _root_.mul_assoc]

end Atlas.G2.TernaryLocals.CharacterGeometry.InvolutionConjugacy
