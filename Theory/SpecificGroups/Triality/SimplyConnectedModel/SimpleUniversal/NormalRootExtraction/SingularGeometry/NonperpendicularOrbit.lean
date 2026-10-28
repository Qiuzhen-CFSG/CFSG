module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The nonperpendicular orbit argument is adapted from
Atlas/LinearGroups/Orthogonal/NonperpendicularOrbit.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: coordinate elimination in CFSG's hyperbolic module, followed by
lifting elementary isometries through the native Clifford Spin action.
-/

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.SingularGeometry.Relations
import Mathlib.Tactic

/-!
# The nonperpendicular orbit of the base-line stabilizer

A singular line nonperpendicular to the base has a representative whose
zeroth second-summand coordinate is one. Upper roots with indices `0,j`
clear its other second coordinates, and skew-upper roots with indices `j,0`
clear the corresponding first coordinates. Singularity forces the remaining
first coordinate to vanish. All these elementary isometries fix the base
vector. Lifting through the Spin cover therefore carries every such line
to the line through `f₀` inside the base-line stabilizer.

This proves the nonperpendicular stabilizer orbit used in the classical
split type-D geometry underlying GLS3, 1.10.1(b),
`refs/KGroup/GLS3/Chapter1.tex`. The proof works in every characteristic.
-/

@[expose] public section
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Triality.SimplyConnected.NormalRootExtraction
open Theory.AlgebraicGroup Theory.AlgebraicGroup.EvenOrthogonalElementary
variable (k : Type*) [Field k]

private lemma exists_nonperpendicular_second_basis (v : QuadraticSpace k)
    (hv0 : v.2 0 = 1) :
    ∃ u : quadraticIsometrySubgroup (quadraticForm k),
      u ∈ evenOrthogonalElementarySubgroup 4 ∧
      (u.1 v).2 = Pi.single 0 1 ∧
      u.1 (baseVector k) = baseVector k := by
  let u := hyperbolicUpperRootPoint 4 0 1 (by decide) (v.2 1) *
    hyperbolicUpperRootPoint 4 0 2 (by decide) (v.2 2) *
    hyperbolicUpperRootPoint 4 0 3 (by decide) (v.2 3)
  have hu : u ∈ evenOrthogonalElementarySubgroup 4 :=
    mul_mem (mul_mem (upper_mem _ _ _ _ _) (upper_mem _ _ _ _ _))
      (upper_mem _ _ _ _ _)
  refine ⟨u, hu, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [u, upper_apply, hv0]
  · apply Prod.ext <;> funext i
    · simp [u, upper_apply, baseVector]
    · simp [u, upper_apply, baseVector]

private lemma exists_nonperpendicular_clear_first (w : QuadraticSpace k)
    (hw0 : w.2 0 = 1) (hwj : ∀ j : Fin 4, j ≠ 0 → w.2 j = 0) :
    ∃ s : quadraticIsometrySubgroup (quadraticForm k),
      s ∈ evenOrthogonalElementarySubgroup 4 ∧
      s.1 (baseVector k) = baseVector k ∧
      (s.1 w).2 = w.2 ∧
      (s.1 w).1 1 = 0 ∧ (s.1 w).1 2 = 0 ∧ (s.1 w).1 3 = 0 := by
  let s := hyperbolicSkewUpperRootPoint 4 1 0 (by decide) (-w.1 1) *
    hyperbolicSkewUpperRootPoint 4 2 0 (by decide) (-w.1 2) *
    hyperbolicSkewUpperRootPoint 4 3 0 (by decide) (-w.1 3)
  have hs : s ∈ evenOrthogonalElementarySubgroup 4 :=
    mul_mem (mul_mem (skewUpper_mem _ _ _ _ _) (skewUpper_mem _ _ _ _ _))
      (skewUpper_mem _ _ _ _ _)
  have hcoord : (s.1 w).1 = w.1 +
      ((-w.1 1) * w.2 0) • Pi.single 1 1 -
      ((-w.1 1) * w.2 1) • Pi.single 0 1 +
      ((-w.1 2) * w.2 0) • Pi.single 2 1 -
      ((-w.1 2) * w.2 2) • Pi.single 0 1 +
      ((-w.1 3) * w.2 0) • Pi.single 3 1 -
      ((-w.1 3) * w.2 3) • Pi.single 0 1 := by
    funext i
    fin_cases i <;> simp [s, skewUpper_apply, hw0, hwj]
  refine ⟨s, hs, ?_, ?_, ?_, ?_, ?_⟩
  · apply Prod.ext <;> funext i
    · simp [s, skewUpper_apply, baseVector]
    · simp [s, skewUpper_apply, baseVector]
  · funext i
    simp [s, skewUpper_apply]
  · rw [hcoord]
    simp [hw0]
  · rw [hcoord]
    simp [hw0]
  · rw [hcoord]
    simp [hw0]

private lemma exists_elementary_map_normalized_nonperpendicular (v : QuadraticSpace k)
    (hv0 : v.2 0 = 1) (hqv : quadraticForm k v = 0) :
    ∃ g : quadraticIsometrySubgroup (quadraticForm k),
      g ∈ evenOrthogonalElementarySubgroup 4 ∧
      g.1 v = singularF k 0 ∧ g.1 (baseVector k) = baseVector k := by
  obtain ⟨u, hu, huv, hu_base⟩ := exists_nonperpendicular_second_basis k v hv0
  let w := u.1 v
  have hw0 : w.2 0 = 1 := by
    change (u.1 v).2 0 = 1
    rw [huv]
    simp
  have hwj : ∀ j : Fin 4, j ≠ 0 → w.2 j = 0 := by
    intro j hj
    change (u.1 v).2 j = 0
    rw [huv]
    simp [hj]
  obtain ⟨s, hs, hs_base, hs_y, hs1, hs2, hs3⟩ :=
    exists_nonperpendicular_clear_first k w hw0 hwj
  have hs0 : (s.1 w).1 0 = 0 := by
    have hq : quadraticForm k (s.1 w) = 0 := by
      exact ((mem_quadraticIsometrySubgroup _ _).mp s.prop w).trans
        (((mem_quadraticIsometrySubgroup _ _).mp u.prop v).trans hqv)
    simp only [quadraticForm, hyperbolicForm_apply] at hq
    rw [hs_y] at hq
    simpa [hw0, hwj, hs1, hs2, hs3, Fin.sum_univ_succ] using hq
  have hfinal : s.1 w = singularF k 0 := by
    apply Prod.ext
    · funext i
      fin_cases i
      · simpa [singularF] using hs0
      · simpa [singularF] using hs1
      · simpa [singularF] using hs2
      · simpa [singularF] using hs3
    · rw [hs_y]
      funext i
      fin_cases i <;> simp [singularF, hw0, hwj]
  refine ⟨s * u, mul_mem hs hu, ?_, ?_⟩
  · change s.1 (u.1 v) = _
    exact hfinal
  · rw [point_mul_apply, hu_base, hs_base]

variable [IsAlgClosed k]

private lemma exists_nonperpendicular_stabilizer_lift
    (g : quadraticIsometrySubgroup (quadraticForm k))
    (hg : g ∈ evenOrthogonalElementarySubgroup 4)
    (hfix : g.1 (baseVector k) = baseVector k) :
    ∃ x : MulAction.stabilizer (Points k) (baseLine k),
      (naturalAction k x.val).val = g := by
  obtain ⟨x, hx⟩ := exists_naturalAction_eq_of_elementary k g hg
  have hbase : x • baseLine k = baseLine k := by
    apply Subtype.ext
    change (naturalAction k x).val • Projectivization.mk k (baseVector k) _ = _
    rw [Projectivization.smul_mk]
    change Projectivization.mk k ((naturalAction k x).val (baseVector k)) _ = _
    have hxv := congrArg (fun z : quadraticIsometrySubgroup (quadraticForm k) =>
      z.1 (baseVector k)) hx
    simpa only [hxv, hfix] using (show Projectivization.mk k (baseVector k)
      (baseVector_ne_zero k) = (baseLine k).val from by rfl)
  exact ⟨⟨x, hbase⟩, by simpa using hx⟩

private lemma exists_nonperpendicular_map_fLine (p : SingularLines k)
    (hp : ¬ SingularPerp k (baseLine k) p) :
    ∃ x : MulAction.stabilizer (Points k) (baseLine k),
      x • p = fLine k 0 := by
  have hp0 : p.val.rep.2 0 ≠ 0 := by
    intro h
    exact hp ((singularPerp_base_iff k p).mpr h)
  let a := p.val.rep.2 0
  let v := a⁻¹ • p.val.rep
  have hv0 : v.2 0 = 1 := by
    simp [v, a, hp0]
  have hqv : quadraticForm k v = 0 := by
    dsimp [v]
    rw [(quadraticForm k).map_smul]
    simp [p.prop]
  obtain ⟨g, hg, hgv, hgb⟩ :=
    exists_elementary_map_normalized_nonperpendicular k v hv0 hqv
  obtain ⟨x, hx⟩ := exists_nonperpendicular_stabilizer_lift k g hg hgb
  have hscaled : (naturalAction k x).val p.val.rep = a • singularF k 0 := by
    have hlin : a⁻¹ • (naturalAction k x).val p.val.rep = singularF k 0 := by
      rw [← map_smul]
      have hgv' : (naturalAction k x).val v = singularF k 0 := by
        simpa only [hx] using hgv
      simpa [v] using hgv'
    calc
      (naturalAction k x).val p.val.rep =
          a • (a⁻¹ • (naturalAction k x).val p.val.rep) := by
        rw [smul_smul, mul_inv_cancel₀ hp0, one_smul]
      _ = a • singularF k 0 := by rw [hlin]
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change (naturalAction k x).val • p.val = (fLine k 0).val
  rw [← Projectivization.mk_rep p.val, Projectivization.smul_mk]
  change Projectivization.mk k ((naturalAction k x).val p.val.rep) _ = (fLine k 0).val
  have hscalar : Projectivization.mk k (a • singularF k 0)
      (smul_ne_zero hp0 (singularF_ne_zero k 0)) = (fLine k 0).val := by
    rw [fLine]
    apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).2
    exact ⟨Units.mk0 a hp0, rfl⟩
  simpa only [hscaled] using hscalar

/-- The base-line stabilizer is transitive on singular lines nonperpendicular
 to the base. This holds over algebraically closed fields in every characteristic. -/
theorem singularLines_base_nonperpendicular_transitive (p q : SingularLines k)
    (hp : ¬ SingularPerp k (baseLine k) p)
    (hq : ¬ SingularPerp k (baseLine k) q) :
    ∃ g : MulAction.stabilizer (Points k) (baseLine k), g • p = q := by
  obtain ⟨xp, hpmap⟩ := exists_nonperpendicular_map_fLine k p hp
  obtain ⟨xq, hqmap⟩ := exists_nonperpendicular_map_fLine k q hq
  refine ⟨xq⁻¹ * xp, ?_⟩
  rw [mul_smul, hpmap, ← hqmap, ← mul_smul, inv_mul_cancel, one_smul]

end Triality.SimplyConnected.NormalRootExtraction
