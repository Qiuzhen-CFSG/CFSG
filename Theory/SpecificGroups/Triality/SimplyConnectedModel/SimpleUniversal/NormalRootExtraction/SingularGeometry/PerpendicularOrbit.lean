module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The geometric transport statement and projective assembly are adapted from
Atlas/LinearGroups/Orthogonal/SingularPrimitiveDGeometry.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: prove transport by rank-four coordinate root elimination and lift
through the native CFSG Clifford Spin natural action.
-/

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.SingularGeometry.Relations
import Mathlib.Tactic

/-!
# The perpendicular orbit of the Spin base-line stabilizer

An elementary isometry fixing e₀ carries any singular vector perpendicular to
but independent of e₀ to e₁. Skew upper roots first produce a nonzero
first-summand coordinate away from 0. Upper roots move that pivot to 1, clear
the other first-summand coordinates and normalize the pivot. Lower roots then
clear coordinates 2 and 3 of the second summand; perpendicularity and
singularity force coordinates 0 and 1 to vanish. Every step fixes e₀.

Composing two such transports and lifting through the existing Spin cover
proves transitivity of the base-line stabilizer on the other perpendicular
singular lines. The vector calculation works over every field, and the Spin
lift only needs algebraic closure; there is no characteristic restriction.

This is the perpendicular suborbit calculation used in the type-D simplicity
argument underlying GLS3, Chapter 1, 1.10.1(b), with the orthogonal and Spin
conventions of 1.10.7 (`refs/KGroup/GLS3/Chapter1.tex`). It assumes neither
primitivity nor simplicity of the Spin action.
-/

public section
noncomputable section
namespace Triality.SimplyConnected.NormalRootExtraction
open Theory.AlgebraicGroup Theory.AlgebraicGroup.EvenOrthogonalElementary
open scoped LinearAlgebra.Projectivization
variable (k : Type*) [Field k]

private lemma upper_fixes_base (i j : Fin 4) (hij : i ≠ j) (hj : j ≠ 0) (a : k) :
    (hyperbolicUpperRootPoint 4 i j hij a).val (baseVector k) = baseVector k := by
  simp [upper_apply, baseVector, hj]

private lemma skewUpper_fixes_base (i j : Fin 4) (hij : i ≠ j) (a : k) :
    (hyperbolicSkewUpperRootPoint 4 i j hij a).val (baseVector k) = baseVector k := by
  simp [skewUpper_apply, baseVector]

private lemma fixed_base_second_zero
    (g : quadraticIsometrySubgroup (quadraticForm k))
    (hg : g.val (baseVector k) = baseVector k)
    (v : QuadraticSpace k) (hv : v.2 0 = 0) : (g.val v).2 0 = 0 := by
  have hpolar : (quadraticForm k).polarBilin (g.val (baseVector k)) (g.val v) =
      (quadraticForm k).polarBilin (baseVector k) v := by
    have hq := (mem_quadraticIsometrySubgroup _ _).mp g.prop
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hq]
  rw [hg] at hpolar
  simp only [quadraticForm, hyperbolicForm_polar] at hpolar
  simpa [baseVector, Pi.single_apply, hv] using hpolar

private lemma exists_perp_nonzero_first (v : QuadraticSpace k)
    (hv : v ∉ Submodule.span k {baseVector k}) (hy : v.2 0 = 0) :
    ∃ g : quadraticIsometrySubgroup (quadraticForm k),
      g ∈ evenOrthogonalElementarySubgroup 4 ∧ g.val (baseVector k) = baseVector k ∧
      ∃ i, i ≠ 0 ∧ (g.val v).1 i ≠ 0 := by
  classical
  by_cases hx : ∃ i, i ≠ 0 ∧ v.1 i ≠ 0
  · exact ⟨1, one_mem _, rfl, hx⟩
  have hxzero (i : Fin 4) (hi : i ≠ 0) : v.1 i = 0 := by
    by_contra h
    exact hx ⟨i, hi, h⟩
  obtain ⟨j, hj0, hj⟩ : ∃ j, j ≠ 0 ∧ v.2 j ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hv
    apply Submodule.mem_span_singleton.mpr
    refine ⟨v.1 0, ?_⟩
    apply Prod.ext
    · funext i
      by_cases hi : i = 0
      · subst i; simp [baseVector]
      · simp [baseVector, hi, hxzero i hi]
    · funext i
      by_cases hi : i = 0
      · subst i; simpa [baseVector] using hy.symm
      · simpa [baseVector] using (hn i hi).symm
  obtain ⟨i, hi0, hij⟩ : ∃ i : Fin 4, i ≠ 0 ∧ i ≠ j := by
    by_cases hj1 : j = 1
    · exact ⟨2, by decide, by simp [hj1]⟩
    · exact ⟨1, by decide, Ne.symm hj1⟩
  refine ⟨hyperbolicSkewUpperRootPoint 4 i j hij 1, skewUpper_mem _ _ _ _ _,
    skewUpper_fixes_base k i j hij 1, i, hi0, ?_⟩
  simpa [skewUpper_apply, hxzero i hi0, Ne.symm hij] using hj

private lemma exists_perp_pivot (v : QuadraticSpace k)
    (hv : v ∉ Submodule.span k {baseVector k}) (hy : v.2 0 = 0) :
    ∃ g : quadraticIsometrySubgroup (quadraticForm k),
      g ∈ evenOrthogonalElementarySubgroup 4 ∧ g.val (baseVector k) = baseVector k ∧
      (g.val v).1 1 ≠ 0 := by
  obtain ⟨g, hg, hfix, i, hi0, hi⟩ := exists_perp_nonzero_first k v hv hy
  by_cases h : (g.val v).1 1 ≠ 0
  · exact ⟨g, hg, hfix, h⟩
  have h1 : (g.val v).1 1 = 0 := not_ne_iff.mp h
  have h1i : (1 : Fin 4) ≠ i := by rintro rfl; exact hi h1
  refine ⟨hyperbolicUpperRootPoint 4 1 i h1i 1 * g,
    mul_mem (upper_mem _ _ _ _ _) hg, ?_, ?_⟩
  · rw [point_mul_apply, hfix, upper_fixes_base k 1 i h1i hi0]
  · simpa [upper_apply, h1] using hi

private lemma exists_perp_first_basis (v : QuadraticSpace k) (hv : v.1 1 ≠ 0) :
    ∃ g : quadraticIsometrySubgroup (quadraticForm k),
      g ∈ evenOrthogonalElementarySubgroup 4 ∧ g.val (baseVector k) = baseVector k ∧
      (g.val v).1 = Pi.single 1 1 := by
  let a := v.1 1
  let h := hyperbolicUpperRootPoint 4 0 1 (by decide) (-v.1 0 / a) *
    hyperbolicUpperRootPoint 4 2 1 (by decide) (-v.1 2 / a) *
    hyperbolicUpperRootPoint 4 3 1 (by decide) (-v.1 3 / a)
  have hh : h ∈ evenOrthogonalElementarySubgroup 4 :=
    mul_mem (mul_mem (upper_mem _ _ _ _ _) (upper_mem _ _ _ _ _))
      (upper_mem _ _ _ _ _)
  have hhfix : h.val (baseVector k) = baseVector k := by
    simp [h, upper_apply, baseVector]
  have hx : (h.val v).1 = Pi.single 1 a := by
    funext i
    fin_cases i <;>
      simp [h, upper_apply, a] <;> field_simp [hv] <;> ring
  let s := hyperbolicUpperRootPoint 4 2 1 (by decide) (-1 : k) *
    hyperbolicUpperRootPoint 4 1 2 (by decide) (1 - a) *
    hyperbolicUpperRootPoint 4 2 1 (by decide) a⁻¹
  have hs : s ∈ evenOrthogonalElementarySubgroup 4 :=
    mul_mem (mul_mem (upper_mem _ _ _ _ _) (upper_mem _ _ _ _ _))
      (upper_mem _ _ _ _ _)
  have hsfix : s.val (baseVector k) = baseVector k := by
    simp [s, upper_apply, baseVector]
  refine ⟨s * h, mul_mem hs hh, ?_, ?_⟩
  · rw [point_mul_apply, hhfix, hsfix]
  · rw [point_mul_apply]
    funext i
    fin_cases i <;> simp [s, upper_apply, hx, a, hv]

/-- An elementary isometry fixing e₀ carries each singular vector in e₀-perp,
independent of e₀, to e₁. This vector calculation holds over every field. -/
theorem exists_elementary_fix_base_map_perpendicular (v : QuadraticSpace k)
    (hv : v ∉ Submodule.span k {baseVector k})
    (hqv : quadraticForm k v = 0) (hy : v.2 0 = 0) :
    ∃ g : quadraticIsometrySubgroup (quadraticForm k),
      g ∈ evenOrthogonalElementarySubgroup 4 ∧ g.val (baseVector k) = baseVector k ∧
      g.val v = singularE k 1 := by
  obtain ⟨g, hg, hgfix, hpivot⟩ := exists_perp_pivot k v hv hy
  obtain ⟨h, hh, hhfix, hfirst⟩ := exists_perp_first_basis k (g.val v) hpivot
  let w := (h * g).val v
  have hw : w.1 = Pi.single 1 1 := hfirst
  have hfix : (h * g).val (baseVector k) = baseVector k := by
    rw [point_mul_apply, hgfix, hhfix]
  have hy0 : w.2 0 = 0 := fixed_base_second_zero k (h * g) hfix v hy
  have hq : hyperbolicForm 4 w = 0 := by
    rw [(mem_quadraticIsometrySubgroup _ _).1 (h * g).2, hqv]
  have hy1 : w.2 1 = 0 := by
    simpa [hyperbolicForm_apply, hw, Pi.single_apply] using hq
  let s := hyperbolicLowerRootPoint 4 2 1 (by decide) (-w.2 2) *
    hyperbolicLowerRootPoint 4 3 1 (by decide) (-w.2 3)
  have hs : s ∈ evenOrthogonalElementarySubgroup 4 :=
    mul_mem (lower_mem _ _ _ _ _) (lower_mem _ _ _ _ _)
  have hsfix : s.val (baseVector k) = baseVector k := by
    simp [s, lower_apply, baseVector]
  refine ⟨s * (h * g), mul_mem hs (mul_mem hh hg), ?_, ?_⟩
  · rw [point_mul_apply, hfix, hsfix]
  · change s.val w = _
    apply Prod.ext
    · simpa [s, lower_apply, singularE] using hw
    · funext i
      fin_cases i <;> simp [s, lower_apply, hw, hy0, hy1, singularE]

private lemma rep_not_span_base (p : SingularLines k) (hp : p ≠ baseLine k) :
    p.val.rep ∉ Submodule.span k {baseVector k} := by
  intro h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  apply hp
  apply Subtype.ext
  change p.val = Projectivization.mk k (baseVector k) _
  rw [← Projectivization.mk_rep p.val]
  exact (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr ⟨a, ha⟩

variable [IsAlgClosed k]

/-- The stabilizer of the base singular line is transitive on the other
singular lines perpendicular to it, under the native Clifford Spin action. -/
theorem singularLines_base_perpendicular_transitive (p q : SingularLines k)
    (hp : p ≠ baseLine k) (hq : q ≠ baseLine k)
    (hpp : SingularPerp k (baseLine k) p) (hpq : SingularPerp k (baseLine k) q) :
    ∃ g : MulAction.stabilizer (Points k) (baseLine k), g • p = q := by
  obtain ⟨g, hg, hgfix, hgp⟩ := exists_elementary_fix_base_map_perpendicular k
    p.val.rep (rep_not_span_base k p hp) p.prop ((singularPerp_base_iff k p).mp hpp)
  obtain ⟨h, hh, hhfix, hhq⟩ := exists_elementary_fix_base_map_perpendicular k
    q.val.rep (rep_not_span_base k q hq) q.prop ((singularPerp_base_iff k q).mp hpq)
  obtain ⟨x, hx⟩ := exists_naturalAction_eq_of_elementary k (h⁻¹ * g)
    (mul_mem (inv_mem hh) hg)
  have hfix : (naturalAction k x).val (baseVector k) = baseVector k := by
    rw [hx, point_mul_apply, hgfix]
    change h.val.symm (baseVector k) = baseVector k
    simpa only [hhfix] using h.val.symm_apply_apply (baseVector k)
  have hlinefix : x • baseLine k = baseLine k := by
    apply Subtype.ext
    change (naturalAction k x).val • Projectivization.mk k (baseVector k) _ =
      Projectivization.mk k (baseVector k) _
    rw [Projectivization.smul_mk]
    change Projectivization.mk k ((naturalAction k x).val (baseVector k)) _ = _
    simp only [hfix]
  refine ⟨⟨x, hlinefix⟩, singularLines_smul_eq_of_rep k x p q ?_⟩
  rw [hx, point_mul_apply, hgp, ← hhq]
  exact h.val.symm_apply_apply _

end Triality.SimplyConnected.NormalRootExtraction
