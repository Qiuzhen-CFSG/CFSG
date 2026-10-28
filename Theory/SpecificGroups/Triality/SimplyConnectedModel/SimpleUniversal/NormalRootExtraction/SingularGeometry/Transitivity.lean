module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.SingularLines
public import Theory.AlgebraicGroup.RootSystems.EvenOrthogonalElementaryGeneration.Coordinates
import Mathlib.Tactic

/-!
# Transitivity on nonzero singular vectors and singular lines

Coordinate root matrices first produce a nonzero first-summand coordinate,
then clear that summand and normalize its pivot. Lower roots clear the second
summand; singularity forces its remaining coordinate to vanish. Thus elementary
orthogonal matrices carry every nonzero singular vector to the standard vector.
The existing Spin-cover surjection lifts them to the given Clifford Spin carrier.

This extends the coordinate elimination of
`EvenOrthogonalElementaryGeneration.Coordinates` to singular vectors and supplies
the transitivity used in the geometric type-D argument of GLS3, 1.10.1(b).
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.NormalRootExtraction
open Theory.AlgebraicGroup Theory.AlgebraicGroup.EvenOrthogonalElementary
open scoped LinearAlgebra.Projectivization
variable (k : Type*) [Field k]

private lemma exists_nonzero_first (v : QuadraticSpace k) (hv : v ≠ 0) :
    ∃ g : quadraticIsometrySubgroup (quadraticForm k),
      g ∈ evenOrthogonalElementarySubgroup 4 ∧ ∃ i, (g.1 v).1 i ≠ 0 := by
  classical
  by_cases hx : ∃ i, v.1 i ≠ 0
  · exact ⟨1, one_mem _, hx⟩
  push Not at hx
  obtain ⟨j, hj⟩ : ∃ j, v.2 j ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hv
    ext i
    · exact hx i
    · exact hn i
  obtain ⟨i, hij⟩ : ∃ i : Fin 4, i ≠ j := exists_ne j
  refine ⟨hyperbolicSkewUpperRootPoint 4 i j hij 1, skewUpper_mem _ _ _ _ _, i, ?_⟩
  simpa [skewUpper_apply, hx, Ne.symm hij] using hj

private lemma exists_singular_pivot (v : QuadraticSpace k) (hv : v ≠ 0) :
    ∃ g : quadraticIsometrySubgroup (quadraticForm k),
      g ∈ evenOrthogonalElementarySubgroup 4 ∧ (g.1 v).1 0 ≠ 0 := by
  obtain ⟨g, hg, i, hi⟩ := exists_nonzero_first k v hv
  by_cases h : (g.1 v).1 0 ≠ 0
  · exact ⟨g, hg, h⟩
  have h0 : (g.1 v).1 0 = 0 := not_ne_iff.mp h
  have hi0 : (0 : Fin 4) ≠ i := by rintro rfl; exact hi h0
  refine ⟨hyperbolicUpperRootPoint 4 0 i hi0 1 * g,
    mul_mem (upper_mem _ _ _ _ _) hg, ?_⟩
  simpa [upper_apply, h0] using hi

private lemma exists_first_basis (v : HyperbolicSpace k 4) (hv : v.1 0 ≠ 0) :
    ∃ g : quadraticIsometrySubgroup (hyperbolicForm (k := k) 4),
      g ∈ evenOrthogonalElementarySubgroup 4 ∧ (g.1 v).1 = Pi.single 0 1 := by
  let a := v.1 0
  let h := hyperbolicUpperRootPoint 4 1 0 (by decide) (-v.1 1 / a) *
    hyperbolicUpperRootPoint 4 2 0 (by decide) (-v.1 2 / a) *
    hyperbolicUpperRootPoint 4 3 0 (by decide) (-v.1 3 / a)
  have hh : h ∈ evenOrthogonalElementarySubgroup 4 :=
    mul_mem (mul_mem (upper_mem _ _ _ _ _) (upper_mem _ _ _ _ _))
      (upper_mem _ _ _ _ _)
  have hx : (h.1 v).1 = Pi.single 0 a := by
    funext i
    fin_cases i <;>
      simp [h, upper_apply, a] <;> field_simp [hv] <;> ring
  let s := hyperbolicUpperRootPoint 4 1 0 (by decide) (-1 : k) *
    hyperbolicUpperRootPoint 4 0 1 (by decide) (1 - a) *
    hyperbolicUpperRootPoint 4 1 0 (by decide) a⁻¹
  have hs : s ∈ evenOrthogonalElementarySubgroup 4 :=
    mul_mem (mul_mem (upper_mem _ _ _ _ _) (upper_mem _ _ _ _ _))
      (upper_mem _ _ _ _ _)
  refine ⟨s * h, mul_mem hs hh, ?_⟩
  rw [point_mul_apply]
  funext i
  fin_cases i <;> simp [s, upper_apply, hx, a, hv]

/-- Every nonzero singular vector can be carried to the standard vector by coordinate roots. -/
theorem exists_elementary_map_singular (v : QuadraticSpace k)
    (hv : v ≠ 0) (hqv : quadraticForm k v = 0) :
    ∃ g : quadraticIsometrySubgroup (quadraticForm k),
      g ∈ evenOrthogonalElementarySubgroup 4 ∧ g.1 v = baseVector k := by
  obtain ⟨g, hg, hpivot⟩ := exists_singular_pivot k v hv
  obtain ⟨h, hh, hfirst⟩ := exists_first_basis k (g.1 v) hpivot
  let w := (h * g).1 v
  have hw : w.1 = Pi.single 0 1 := hfirst
  have hq : hyperbolicForm 4 w = 0 := by
    rw [(mem_quadraticIsometrySubgroup _ _).1 (h * g).2, hqv]
  have hy0 : w.2 0 = 0 := by
    simpa [hyperbolicForm_apply, hw, Pi.single_apply] using hq
  let s := hyperbolicLowerRootPoint 4 1 0 (by decide) (-w.2 1) *
    hyperbolicLowerRootPoint 4 2 0 (by decide) (-w.2 2) *
    hyperbolicLowerRootPoint 4 3 0 (by decide) (-w.2 3)
  have hs : s ∈ evenOrthogonalElementarySubgroup 4 :=
    mul_mem (mul_mem (lower_mem _ _ _ _ _) (lower_mem _ _ _ _ _))
      (lower_mem _ _ _ _ _)
  refine ⟨s * (h * g), mul_mem hs (mul_mem hh hg), ?_⟩
  change s.1 w = _
  apply Prod.ext
  · simpa [s, lower_apply, baseVector] using hw
  · funext i
    fin_cases i <;> simp [s, lower_apply, hw, hy0, baseVector]

variable [IsAlgClosed k]

/-- The already constructed Spin cover lifts every elementary orthogonal matrix. -/
theorem exists_naturalAction_eq_of_elementary
    (g : quadraticIsometrySubgroup (quadraticForm k))
    (hg : g ∈ evenOrthogonalElementarySubgroup 4) :
    ∃ x : Points k, naturalAction k x = g := by
  obtain ⟨x, hx⟩ := toOmega_surjective k ⟨g, le_commutator 4 hg⟩
  exact ⟨x, congrArg Subtype.val hx⟩

/-- Equality on representatives gives equality of their singular lines. -/
theorem singularLines_smul_eq_of_rep (g : Points k) (p q : SingularLines k)
    (h : (naturalAction k g).val p.val.rep = q.val.rep) : g • p = q := by
  apply Subtype.ext
  change (naturalAction k g).val • p.val = q.val
  rw [← Projectivization.mk_rep p.val, Projectivization.smul_mk]
  change Projectivization.mk k ((naturalAction k g).val p.val.rep) _ = q.val
  simpa only [h] using Projectivization.mk_rep q.val

/-- Spin is transitive on the singular projective points of its natural module. -/
theorem singularLines_pretransitive : MulAction.IsPretransitive (Points k) (SingularLines k) := by
  constructor
  intro p q
  obtain ⟨g, hg, hp⟩ := exists_elementary_map_singular k p.val.rep p.val.rep_nonzero p.prop
  obtain ⟨h, hh, hq⟩ := exists_elementary_map_singular k q.val.rep q.val.rep_nonzero q.prop
  obtain ⟨x, hx⟩ := exists_naturalAction_eq_of_elementary k (h⁻¹ * g)
    (mul_mem (inv_mem hh) hg)
  refine ⟨x, singularLines_smul_eq_of_rep k x p q ?_⟩
  rw [hx, point_mul_apply, hp, ← hq]
  exact h.val.symm_apply_apply _

end Triality.SimplyConnected.NormalRootExtraction
