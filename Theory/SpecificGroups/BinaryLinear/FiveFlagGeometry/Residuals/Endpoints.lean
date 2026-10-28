module

public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.SpecificGroups.BinaryLinear.FiveParabolicStabilizer
public import Theory.SpecificGroups.BinaryLinear.SylowTransvections
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Quotient
public import Theory.GroupTheory.Commutator.PerfectQuotient
public import Mathlib.Tactic.Module

/-!
# Perfectness of the binary five-dimensional end parabolics

The point-stabilizer kernel consists of rank-one transvections. Each is a
commutator of two transvections fixing the point: choose a second vector in
the defining functional's kernel and a functional separating it from the
fixed line. The quotient action is onto GL₄(2), which is perfect, so the whole
point stabilizer is perfect. Inverse transpose gives the hyperplane case.

These statements concern the actual stabilizers, including their radicals.
They supply the residual calculation for Aschbacher–Smith, combined manuscript
(1 March 2004), A.3.12(5), printed pp.47–48, and 1.3.9, printed p.514.
The transvection identity follows the calculation in `BinaryLinear.NestedRadicals`.
-/

public section

open Subgroup
open scoped commutatorElement
namespace BinaryLinear.FiveFlagGeometry
open OuterCyclic
open Theory.LinearAlgebra

private theorem transvection_cross (w y : Space 5)
    (α β : Space 5 →ₗ[ZMod 2] ZMod 2)
    (hαw : α w = 0) (hβw : β w = 0) (hβy : β y = 0) (hαy : α y = 1) :
    ⁅transvection w α hαw, transvection y β hβy⁆ = transvection w β hβw := by
  apply LinearEquiv.ext
  intro v
  change (v + β v • y + α (v + β v • y) • w +
    β (v + β v • y + α (v + β v • y) • w) • y +
    α (v + β v • y + α (v + β v • y) • w +
      β (v + β v • y + α (v + β v • y) • w) • y) • w) = v + β v • w
  simp only [map_add, map_smul, hαw, hβw, hβy, hαy, smul_eq_mul, mul_zero,
    mul_one, add_zero]
  match_scalars <;> ring_nf <;>
    simp only [show (2 : ZMod 2) = 0 by decide, show (3 : ZMod 2) = 1 by decide,
      mul_zero, mul_one, zero_add]

/-- Every displacement-kernel element is a commutator inside the point stabilizer. -/
theorem point_kernel_le_commutator {v : Space 5} (hv : v ≠ 0) :
    BinaryFivePointStabilizer.kernel v ≤ commutator (BinaryFivePointStabilizer.stabilizer v) := by
  intro g hg
  by_cases hg1 : g = 1
  · exact hg1 ▸ one_mem _
  have hr : g.val ∈ radical (BinaryFivePointStabilizer.line v) :=
    ⟨BinaryFivePointStabilizer.fixes_line v g, (BinaryFivePointStabilizer.mem_kernel_iff v g).mp hg⟩
  obtain ⟨β, _, hβv, he⟩ := exists_transvection_of_mem_line_radical hv hr
    (fun h => hg1 (Subtype.ext h))
  have hline : BinaryFivePointStabilizer.line v ≤ β.ker := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact hβv
  have hlt : BinaryFivePointStabilizer.line v < β.ker := by
    apply lt_of_le_of_ne hline
    intro heq
    have hd := β.finrank_range_add_finrank_ker
    have hb := Submodule.finrank_le β.range
    rw [← heq, finrank_span_singleton hv] at hd
    norm_num [Space] at hd hb
    omega
  obtain ⟨y, hβy, hyv⟩ := SetLike.exists_of_lt hlt
  obtain ⟨α, hαy, hαv⟩ := (BinaryFivePointStabilizer.line v).exists_le_ker_of_notMem hyv
  have hαv0 : α v = 0 := hαv (Submodule.mem_span_singleton_self v)
  have hαy1 : α y = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hαy
  let a : BinaryFivePointStabilizer.stabilizer v := ⟨transvection v α hαv0, by
    change v + α v • v = v
    simp [hαv0]⟩
  let c : BinaryFivePointStabilizer.stabilizer v := ⟨transvection y β hβy, by
    change v + β v • y = v
    simp [hβv]⟩
  have hcomm : ⁅a, c⁆ = g := by
    apply Subtype.ext
    change ⁅transvection v α hαv0, transvection y β hβy⁆ = g.val
    rw [transvection_cross v y α β hαv0 hβv hβy hαy1]
    apply LinearEquiv.ext
    intro x
    exact (he x).symm
  rw [← hcomm]
  exact commutator_mem_commutator (mem_top _) (mem_top _)

/-- The point stabilizer is perfect, including its elementary abelian kernel. -/
theorem pointStabilizer_isPerfect {v : Space 5} (hv : v ≠ 0) :
    Group.IsPerfect (BinaryFivePointStabilizer.stabilizer v) := by
  let b := BinaryFivePointStabilizer.quotientCoordinates v hv (by simp [Space])
  let e : (BinaryFivePointStabilizer.QuotientSpace v ≃ₗ[ZMod 2] BinaryFivePointStabilizer.QuotientSpace v) ≃* LinearGroup 4 :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (BinaryFivePointStabilizer.QuotientSpace v)).symm.trans
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv b).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Space 4)))
  let : Group.IsPerfect (LinearGroup 4) := linearGroup_isPerfect 4 (by decide)
  let : Group.IsPerfect (BinaryFivePointStabilizer.QuotientSpace v ≃ₗ[ZMod 2] BinaryFivePointStabilizer.QuotientSpace v) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  constructor
  have hh := CentralExtension.ker_sup_commutator_eq_top_of_surjective
    (BinaryFivePointStabilizer.quotientAction v) (BinaryFivePointStabilizer.quotientAction_surjective v)
  rwa [sup_eq_right.mpr (point_kernel_le_commutator hv)] at hh

/-- Over the binary field, stabilizing a nonzero vector's line fixes that vector. -/
theorem pointParabolic_eq_stabilizer {v : Space 5} (hv : v ≠ 0) :
    parabolic (Submodule.span (ZMod 2) {v}) = BinaryFivePointStabilizer.stabilizer v := by
  ext g
  constructor
  · intro hg
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      ((hg v).mpr (Submodule.mem_span_singleton_self v))
    have ha0 : a ≠ 0 := by
      intro hz
      exact hv (g.map_eq_zero_iff.mp (by simpa [hz] using ha.symm))
    have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
    simpa [ha1, BinaryFivePointStabilizer.mem_stabilizer] using ha.symm
  · intro hg x
    have hfix : g v = v := hg
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
      exact Submodule.mem_span_singleton.mpr ⟨a, g.injective (by simpa [hfix] using ha)⟩
    · intro hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      simpa [map_smul, hfix] using Submodule.smul_mem
        (Submodule.span (ZMod 2) {v}) a (Submodule.mem_span_singleton_self v)

/-- The actual geometric point parabolic is perfect. -/
theorem pointParabolic_isPerfect {v : Space 5} (hv : v ≠ 0) :
    Group.IsPerfect (parabolic (Submodule.span (ZMod 2) {v})) := by
  rw [pointParabolic_eq_stabilizer hv]
  exact pointStabilizer_isPerfect hv

/-- Inverse transpose transfers perfectness to every hyperplane parabolic. -/
theorem hyperplaneParabolic_isPerfect {f : Space 5 →ₗ[ZMod 2] ZMod 2} (hf : f ≠ 0) :
    Group.IsPerfect (parabolic f.ker) := by
  obtain ⟨v, hv, he⟩ := FiveParabolicStabilizer.hyperplane_map_graph hf
  let : Group.IsPerfect ((parabolic f.ker).map (graphLinear 5).toMonoidHom) := by
    rw [he]
    exact pointParabolic_isPerfect hv
  let e := (parabolic f.ker).equivMapOfInjective (graphLinear 5).toMonoidHom
    (graphLinear 5).injective
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

end BinaryLinear.FiveFlagGeometry
