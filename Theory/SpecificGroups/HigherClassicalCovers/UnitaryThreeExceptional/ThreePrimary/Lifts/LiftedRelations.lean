module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Lifts.FiniteRelations
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Lifts.LiftedRelations.Defects
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Lifts.LiftedRelations.Equivariance
import Mathlib.Tactic.FinCases

/-!
# Two cubic defects control the fifteen lifted unitary relations

Use the normalized six root lifts. The two defects are the error in the
`(0,2)` collection relation and the commutator of roots `0` and `3`; both are
actual central kernel elements of cube one. In their central quotient, nine
swaps hold by partial inversion and unitary conjugacy, and the two mixed
commuting swaps follow from the second defect and torus rotation. The first
collection relation and its torus transforms give the remaining four swaps.

This constructs `FiniteDefectRelations` for every perfect central cover of
the prescribed carrier, in particular for the finite covers of degree 27.
It requires neither a kernel exponent assumption nor presentation completeness.
The latter remains an independent input to the existing section assembly.
All projective markings use the original `coordinateProjection`.

Source: the exceptional three-part calculation for Aschbacher--Smith
I.1.4(5), printed p.408; GLS3 §6.1 and its cited multiplier literature.
-/

public noncomputable section
open scoped commutatorElement
open Subgroup PerfectCentralCovering
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts
open LiftedRelations

/-- The finite root-relation contract, with both cubic defects constructed.
Finiteness and the degree-27 restriction are unnecessary for this local result. -/
theorem nonempty_finiteDefectRelations {E : Type*} [Group E] (f : Cover E S) :
    Nonempty (FiniteDefectRelations f) := by
  let L := normalizedRoots f.toMonoidHom f.surjective f.ker_le_center
  let p := L.collectionDefect
  let w := L.mixedDefect
  let D : Subgroup E := zpowers p ⊔ zpowers w
  have hD : D ≤ f.toMonoidHom.ker :=
    sup_le (zpowers_le.mpr L.collectionDefect_mem) (zpowers_le.mpr L.mixedDefect_mem)
  have hnormal : D.Normal := ⟨fun z hz g => by
    rw [mem_center_iff.mp (f.ker_le_center (hD hz)) g, mul_inv_cancel_right]
    exact hz⟩
  let : D.Normal := hnormal
  let q : E →* E ⧸ D := QuotientGroup.mk' D
  let x : Fin 6 → E ⧸ D := fun r => q (L.gen r)
  obtain ⟨T, hT⟩ := f.surjective (torus 1)
  let φ : (E ⧸ D) ≃* (E ⧸ D) := MulAut.conj (q T)
  have hc (r : Fin 6) : x r ^ 3 = 1 := by
    change q (L.gen r) ^ 3 = 1
    rw [← map_pow, L.cubes, map_one]
  have h2 (r : Fin 6) : x r ^ 2 = (x r)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hc]
  have hr (r : Fin 6) : φ (x r) = x (rotatedRoot r) ^ rotationPower r := by
    have hh := congrArg q
      (normalizedRoot_rotates f.toMonoidHom f.surjective f.ker_le_center T hT r)
    simpa only [φ, x, q, L, normalizedRoots, MulAut.conj_apply, QuotientGroup.mk'_apply,
      map_mul, map_inv, map_pow] using hh
  have ha : φ (x 0) = (x 1)⁻¹ := by simpa [rotatedRoot, rotationPower, h2] using hr 0
  have hb : φ (x 1) = x 0 := by simpa [rotatedRoot, rotationPower] using hr 1
  have hcc : φ (x 2) = (x 2)⁻¹ := by simpa [rotatedRoot, rotationPower, h2] using hr 2
  have hd : φ (x 3) = x 4 := by simpa [rotatedRoot, rotationPower] using hr 3
  have he : φ (x 4) = (x 3)⁻¹ := by simpa [rotatedRoot, rotationPower, h2] using hr 4
  have hv : φ (x 5) = (x 5)⁻¹ := by simpa [rotatedRoot, rotationPower, h2] using hr 5
  have hcomm (i j : Fin 6) (hij : ExactPair i j) : Commute (x i) (x j) :=
    (commute_exactPair f.toMonoidHom f.surjective f.ker_le_center L i j hij).map q
  have h02 : x 2 * x 0 = x 0 * x 2 * x 4 ^ 2 * x 5 := by
    have hh : q p = 1 := (QuotientGroup.eq_one_iff (N := D) _).mpr
      (show p ∈ D from by
        change p ∈ zpowers p ⊔ zpowers w
        exact (le_sup_left : zpowers p ≤ zpowers p ⊔ zpowers w) (mem_zpowers p))
    have hh' : x 2 * x 0 = x 0 * x 2 * swapTail x 0 2 := by
      apply mul_inv_eq_one.mp
      simpa only [p, CubicRootLifts.collectionDefect, CubicRootLifts.swapError,
        map_mul, map_inv, map_swapTail] using hh
    simpa [swapTail, mul_assoc] using hh'
  have h03 : Commute (x 0) (x 3) := by
    apply commutatorElement_eq_one_iff_commute.mp
    change ⁅q (L.gen 0), q (L.gen 3)⁆ = 1
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := D) _).mpr
      (show w ∈ D from by
        change w ∈ zpowers p ⊔ zpowers w
        exact (le_sup_right : zpowers w ≤ zpowers p ⊔ zpowers w) (mem_zpowers w))
  have h14 : Commute (x 1) (x 4) := by
    have hh := h03.map φ.toMonoidHom
    change Commute (φ (x 0)) (φ (x 3)) at hh
    rw [ha, hd] at hh
    simpa only [inv_inv] using hh.inv_left
  obtain ⟨h04, h12, h13⟩ := remaining_three_relations
    (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) φ ha hb hcc hd he hv (hc 4) (hc 5)
    (hcomm 2 4 (by simp [ExactPair])) (hcomm 2 5 (by simp [ExactPair]))
    (hcomm 0 5 (by simp [ExactPair])) (hcomm 4 5 (by simp [ExactPair])) h02
  have hs (i j : Fin 6) (hij : i < j) : x j * x i = x i * x j * swapTail x i j := by
    fin_cases i <;> fin_cases j <;> norm_num at hij
    · simpa [swapTail] using (hcomm 0 1 (by simp [ExactPair])).eq.symm
    · simpa [swapTail, mul_assoc] using h02
    · simpa [swapTail] using h03.eq.symm
    · simpa [swapTail] using h04
    · simpa [swapTail] using (hcomm 0 5 (by simp [ExactPair])).eq.symm
    · simpa [swapTail, mul_assoc] using h12
    · simpa [swapTail] using h13
    · simpa [swapTail] using h14.eq.symm
    · simpa [swapTail] using (hcomm 1 5 (by simp [ExactPair])).eq.symm
    · simpa [swapTail] using (hcomm 2 3 (by simp [ExactPair])).eq.symm
    · simpa [swapTail] using (hcomm 2 4 (by simp [ExactPair])).eq.symm
    · simpa [swapTail] using (hcomm 2 5 (by simp [ExactPair])).eq.symm
    · simpa [swapTail] using (hcomm 3 4 (by simp [ExactPair])).eq.symm
    · simpa [swapTail] using (hcomm 3 5 (by simp [ExactPair])).eq.symm
    · simpa [swapTail] using (hcomm 4 5 (by simp [ExactPair])).eq.symm
  refine ⟨{
    roots := L, z := p, w := w,
    z_mem := L.collectionDefect_mem, w_mem := L.mixedDefect_mem,
    z_cube := L.collectionDefect_cube f.surjective f.ker_le_center,
    w_cube := L.mixedDefect_cube f.ker_le_center, swaps := ?_ }⟩
  intro i j hij
  apply (QuotientGroup.eq_one_iff (N := D) _).mp
  change q (L.gen j * L.gen i * (L.gen i * L.gen j * swapTail L.gen i j)⁻¹) = 1
  simpa only [map_mul, map_inv, map_swapTail, mul_inv_eq_one] using hs i j hij

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts
