module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseThreeExclusion.SourceGroups

/-!
# Elementary centralizers of the Case III involution words

In Janko Case III, the first two binary coordinates are fixed by both source
actors `a` and `b`. Their kernel images, together with the actual complement
images of `a` and `b`, therefore form an elementary subgroup of order sixteen.
We construct it as the range of an injective homomorphism from `BinaryFour`;
uniqueness of the original kernel/complement factorization proves injectivity.

The square-one equation for a source word forces its kernel coordinate to be
fixed by its actor. The source matrices then show that either both actor
exponents vanish or the last two kernel coordinates vanish. In the former
case the word is centralized by the elementary kernel, and in the latter by
the constructed elementary subgroup. All conjugations use the source's
literal right-conjugation convention, through `ambient_conjugation_a/b`.

The exported theorem discharges precisely the `helementary` premise of
`CaseThreeExclusion.false_of_source_computations`, without ambient simplicity
or any word-coverage premise.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 1, p.3, DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseThreeExclusion

private def firstTwo : BinaryFour →* BinaryFour where
  toFun v := Multiplicative.ofAdd ![v.toAdd 0, v.toAdd 1, 0, 0]
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private def lastTwo : BinaryFour →* SymmetricFour where
  toFun v := jankoA ^ (v.toAdd 2).val * jankoB ^ (v.toAdd 3).val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private theorem firstTwo_a : ∀ v, jankoSourceA .three (firstTwo v) = firstTwo v := by
  decide +kernel
private theorem firstTwo_b : ∀ v, jankoSourceB .three (firstTwo v) = firstTwo v := by
  decide +kernel
private theorem firstTwo_lastTwo_injective : ∀ v w,
    firstTwo v = firstTwo w → lastTwo v = lastTwo w → v = w := by
  decide +kernel

private def wordAction (v : BinaryFour) (i j : Fin 2) : BinaryFour :=
  let w := if i = 0 then v else jankoSourceA .three v
  if j = 0 then w else jankoSourceB .three w

private theorem wordAction_fixed : ∀ v i j,
    wordAction v i j = v → (i = 0 ∧ j = 0) ∨ (v.toAdd 2 = 0 ∧ v.toAdd 3 = 0) := by
  decide +kernel

private theorem firstTwo_lastTwo_coverage : ∀ (v : BinaryFour) (i j : Fin 2),
    v.toAdd 2 = 0 → v.toAdd 3 = 0 →
    ∃ w, firstTwo w = v ∧ lastTwo w = jankoA ^ i.val * jankoB ^ j.val := by
  decide +kernel

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K)
  (R : JankoCoordinates (D.binaryAction K hK) .three)

private theorem firstTwo_commute_a (v : BinaryFour) :
    Commute (R.ambientBasis D K hK (firstTwo v))
      (jankoAmbientComplement D K hK jankoA) := by
  have h := R.ambient_conjugation_a D K hK (firstTwo v)
  rw [firstTwo_a] at h
  have hh := congrArg (fun x => jankoAmbientComplement D K hK jankoA * x) h
  simpa only [Commute, SemiconjBy, ← mul_assoc, mul_inv_cancel, one_mul] using hh

private theorem firstTwo_commute_b (v : BinaryFour) :
    Commute (R.ambientBasis D K hK (firstTwo v))
      (jankoAmbientComplement D K hK jankoB) := by
  have h := R.ambient_conjugation_b D K hK (firstTwo v)
  rw [firstTwo_b] at h
  have hh := congrArg (fun x => jankoAmbientComplement D K hK jankoB * x) h
  simpa only [Commute, SemiconjBy, ← mul_assoc, mul_inv_cancel, one_mul] using hh

private theorem firstTwo_commute_lastTwo (v w : BinaryFour) :
    Commute (R.ambientBasis D K hK (firstTwo v))
      (jankoAmbientComplement D K hK (lastTwo w)) := by
  change Commute _ (jankoAmbientComplement D K hK
    (jankoA ^ (w.toAdd 2).val * jankoB ^ (w.toAdd 3).val))
  rw [map_mul, map_pow, map_pow]
  exact ((firstTwo_commute_a D K hK R v).pow_right _).mul_right
    ((firstTwo_commute_b D K hK R v).pow_right _)

/-- Coordinates on the actual source subgroup `E₁ × A = ⟨z₁,z₂,a,b⟩`. -/
private noncomputable def fourMap : BinaryFour →* G where
  toFun v := R.ambientBasis D K hK (firstTwo v) *
    jankoAmbientComplement D K hK (lastTwo v)
  map_one' := by simp only [map_one, mul_one]
  map_mul' v w := by
    simp only [map_mul]
    rw [mul_assoc, ← mul_assoc (R.ambientBasis D K hK (firstTwo w)),
      (firstTwo_commute_lastTwo D K hK R w v).eq,
      mul_assoc, ← mul_assoc]

private theorem word_coordinates_injective (v w : BinaryFour) (s t : SymmetricFour)
    (h : R.ambientBasis D K hK v * jankoAmbientComplement D K hK s =
      R.ambientBasis D K hK w * jankoAmbientComplement D K hK t) :
    v = w ∧ s = t := by
  let ev := D.kernelBinaryEquiv.symm (R.basis v)
  let ew := D.kernelBinaryEquiv.symm (R.basis w)
  let ks := (D.complementEquiv K hK).symm s
  let kt := (D.complementEquiv K hK).symm t
  have he : (ev, ks) = (ew, kt) := hK.1 (D.centralizer.subtype_injective h)
  constructor
  · exact R.basis.injective (D.kernelBinaryEquiv.symm.injective (congrArg Prod.fst he))
  · exact (D.complementEquiv K hK).symm.injective (congrArg Prod.snd he)

private theorem fourMap_injective : Function.Injective (fourMap D K hK R) := by
  intro v w h
  obtain ⟨hv, hw⟩ := word_coordinates_injective D K hK R
    (firstTwo v) (firstTwo w) (lastTwo v) (lastTwo w) h
  exact firstTwo_lastTwo_injective v w hv hw

omit [Finite G] in
private theorem range_elementary (f : BinaryFour →* G) : IsElementaryAbelian 2 f.range := by
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  rintro ⟨x, v, rfl⟩
  apply Subtype.ext
  change f v ^ 2 = 1
  rw [← map_pow, show v ^ 2 = 1 from (by
    have hh : ∀ v : BinaryFour, v ^ 2 = 1 := by decide +kernel
    exact hh v), map_one]

omit [Finite G] in
private theorem range_card (f : BinaryFour →* G) (hf : Function.Injective f) :
    Nat.card f.range = 16 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, Nat.card_eq_fintype_card]
  decide

private theorem word_conjugation (v : BinaryFour) (i j : Fin 2) :
    (jankoAmbientComplement D K hK (jankoA ^ i.val * jankoB ^ j.val))⁻¹ *
      R.ambientBasis D K hK v *
      jankoAmbientComplement D K hK (jankoA ^ i.val * jankoB ^ j.val) =
        R.ambientBasis D K hK (wordAction v i j) := by
  fin_cases i <;> fin_cases j
  · simp [wordAction]
  · simpa [wordAction] using R.ambient_conjugation_b D K hK v
  · simpa [wordAction] using R.ambient_conjugation_a D K hK v
  · simp only [pow_one, map_mul, mul_inv_rev]
    calc
      _ = (jankoAmbientComplement D K hK jankoB)⁻¹ *
          ((jankoAmbientComplement D K hK jankoA)⁻¹ * R.ambientBasis D K hK v *
            jankoAmbientComplement D K hK jankoA) *
          jankoAmbientComplement D K hK jankoB := by simp only [mul_assoc]
      _ = _ := by
        rw [R.ambient_conjugation_a, R.ambient_conjugation_b]
        rfl

private theorem involution_word_coordinates (v : BinaryFour) (i j : Fin 2)
    (h : orderOf (sourceHWord D K hK R v i j) = 2) :
    (i = 0 ∧ j = 0) ∨ (v.toAdd 2 = 0 ∧ v.toAdd 3 = 0) := by
  let x := R.ambientBasis D K hK v
  let y := jankoAmbientComplement D K hK (jankoA ^ i.val * jankoB ^ j.val)
  have hx : x * x = 1 := by
    change R.ambientBasis D K hK v * R.ambientBasis D K hK v = 1
    rw [← map_mul, show v * v = 1 from (by
      have hh : ∀ v : BinaryFour, v * v = 1 := by decide +kernel
      exact hh v), map_one]
  have hy : y⁻¹ = y := by
    have hi : ∀ i j : Fin 2, (jankoA ^ i.val * jankoB ^ j.val)⁻¹ =
        jankoA ^ i.val * jankoB ^ j.val := by decide +kernel
    change (jankoAmbientComplement D K hK _)⁻¹ = _
    rw [← map_inv, hi]
  have hsq : (x * y) * (x * y) = 1 := by
    have hh := pow_orderOf_eq_one (sourceHWord D K hK R v i j)
    rw [h, pow_two] at hh
    exact hh
  have hc : y⁻¹ * x * y = x := by
    rw [hy]
    have hh := congrArg (fun z => x * z) hsq
    simpa only [← mul_assoc, hx, one_mul, mul_one] using hh
  apply wordAction_fixed v i j
  apply R.ambientBasis_injective D K hK
  exact (word_conjugation D K hK R v i j).symm.trans hc

omit [Finite G] in
private theorem range_le_centralizer (f : BinaryFour →* G) (v : BinaryFour) :
    f.range ≤ centralizer ({f v} : Set G) := by
  rintro x ⟨w, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  rw [← map_mul, ← map_mul, mul_comm]

/-- Every involution word in Janko Case III is centralized by an actual
ambient elementary abelian subgroup of order sixteen. -/
public theorem sourceHWord_elementary_centralizer (v : BinaryFour) (i j : Fin 2)
    (h : orderOf (sourceHWord D K hK R v i j) = 2) :
    ∃ E : Subgroup G, E ≤ centralizer ({sourceHWord D K hK R v i j} : Set G) ∧
      IsElementaryAbelian 2 E ∧ Nat.card E = 16 := by
  rcases involution_word_coordinates D K hK R v i j h with ⟨rfl, rfl⟩ | ⟨h2, h3⟩
  · refine ⟨sourceE D K hK R, ?_, range_elementary (R.ambientBasis D K hK),
      range_card _ (R.ambientBasis_injective D K hK)⟩
    simpa only [sourceE, sourceHWord, Fin.val_zero, pow_zero, mul_one, map_one] using
      range_le_centralizer (R.ambientBasis D K hK) v
  · obtain ⟨w, hv, ha⟩ := firstTwo_lastTwo_coverage v i j h2 h3
    have hw : fourMap D K hK R w = sourceHWord D K hK R v i j := by
      change R.ambientBasis D K hK (firstTwo w) *
        jankoAmbientComplement D K hK (lastTwo w) = _
      rw [hv, ha]
      rfl
    refine ⟨(fourMap D K hK R).range, ?_, range_elementary _,
      range_card _ (fourMap_injective D K hK R)⟩
    rw [← hw]
    exact range_le_centralizer _ w

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseThreeExclusion
