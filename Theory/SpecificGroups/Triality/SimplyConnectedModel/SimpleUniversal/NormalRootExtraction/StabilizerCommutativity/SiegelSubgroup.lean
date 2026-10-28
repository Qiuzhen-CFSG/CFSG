module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Adapted from Atlas/LinearGroups/Orthogonal/{RootSubgroup,RootSubgroupConjugation}.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917;
see LICENSES/ATLAS-CITATION.cff.
Changes: reuse CFSG's quadratic-isometry carrier and Siegel formulas, and retain
only the parameter subgroup, commutativity and line-stabilizer conjugation.
-/

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Elementary

/-!
# Abelian Siegel subgroups in a singular direction

The perpendicular parameter space maps additively to the actual quadratic
isometry group by the Siegel formula. Its image is therefore abelian.
Covariance and rescaling show that every quadratic isometry stabilizing the
singular line normalizes this image. The argument works in arbitrary
characteristic and uses preservation of the quadratic form itself.

This is the local classical geometry used in the type-D simplicity argument
underlying GLS3, 1.10.1(b), `refs/KGroup/GLS3/Chapter1.tex`.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup
namespace ClassicalOrthogonal.SiegelDirection
open ClassicalOrthogonal.Quadratic
universe u
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (u : V) (hu : Q u = 0)

/-- The additive perpendicular parameters, mapped to actual quadratic isometries. -/
def parameterHom : Multiplicative (LinearMap.ker (Q.polarBilin u)) →*
    quadraticIsometrySubgroup Q where
  toFun v := siegelElement Q u v.toAdd.val hu v.toAdd.prop
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    exact siegel_zero Q u
  map_mul' v w := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact (siegel_add Q u v.toAdd.val w.toAdd.val x hu v.toAdd.prop w.toAdd.prop).symm

/-- The Siegel subgroup in a fixed singular direction. -/
def subgroup : Subgroup (quadraticIsometrySubgroup Q) := (parameterHom Q u hu).range

instance subgroup_isMulCommutative : IsMulCommutative (subgroup Q u hu) := by
  apply IsMulCommutative.of_setLike_mul_comm
  rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

/-- A quadratic isometry stabilizing the singular line conjugates this subgroup
into itself. Covariance transports the parameter and rescaling restores the direction. -/
theorem conj_mem (g : quadraticIsometrySubgroup Q) (c : F) (hc : c ≠ 0)
    (hg : g.val u = c • u) (r : quadraticIsometrySubgroup Q)
    (hr : r ∈ subgroup Q u hu) : g * r * g⁻¹ ∈ subgroup Q u hu := by
  obtain ⟨v, rfl⟩ := hr
  let e : Q.IsometryEquiv Q :=
    { g.val with map_app' := (mem_quadraticIsometrySubgroup Q g.val).mp g.prop }
  have hp : Q.polarBilin (g.val u) (g.val v.toAdd.val) = 0 :=
    (isometry_polar Q e u v.toAdd.val).trans v.toAdd.prop
  rw [hg, map_smul, LinearMap.smul_apply, smul_eq_mul] at hp
  have hv : Q.polarBilin u (g.val v.toAdd.val) = 0 :=
    (mul_eq_zero.mp hp).resolve_left hc
  have hcv : Q.polarBilin u (c • g.val v.toAdd.val) = 0 := by
    rw [map_smul, hv, smul_zero]
  refine ⟨Multiplicative.ofAdd ⟨c • g.val v.toAdd.val, hcv⟩, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change siegel Q u (c • g.val v.toAdd.val) x =
    g.val (siegel Q u v.toAdd.val (g.val.symm x))
  have he := siegel_covariant Q e u v.toAdd.val (g.val.symm x)
  change g.val (siegel Q u v.toAdd.val (g.val.symm x)) =
    siegel Q (g.val u) (g.val v.toAdd.val) (g.val (g.val.symm x)) at he
  rw [LinearEquiv.apply_symm_apply, hg, siegel_scale] at he
  exact he.symm

end ClassicalOrthogonal.SiegelDirection
