module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The line-stabilizer argument is adapted from
Atlas/LinearGroups/Orthogonal/RootPointStabilizer.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: work in CFSG's Clifford Spin carrier, compare its first pinned root
with the Siegel formula, and bound the relative normal closure by its pullback.
-/

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.Stabilizer
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.StabilizerCommutativity.SiegelSubgroup

/-!
# Commutativity of the relative root closure in a singular-line stabilizer

For the native hyperbolic quadratic space, the first simple root matrix is
`E(baseVector, (0, Pi.single 1 a))`. The Siegel transformations in this fixed
singular direction form an abelian subgroup, normalized by every quadratic
isometry preserving its line. Its pullback to Spin is abelian because the
natural action is injective in characteristic two. The normal closure of the
first root group inside the line stabilizer is contained in this pullback;
its image in Spin is consequently abelian.

Only containment is needed. No primitivity, simplicity or root-extraction
hypothesis occurs. This supplies the abelian stabilizer geometry in the
classical type-D argument underlying GLS3, 1.10.1(b),
`refs/KGroup/GLS3/Chapter1.tex`.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup
namespace Triality.SimplyConnected.NormalRootExtraction
open Pinning ClassicalOrthogonal ClassicalOrthogonal.Quadratic
open Theory.AlgebraicGroup.StandardRootSystem
open scoped LinearAlgebra.Projectivization
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

omit [CharP k 2] in
/-- Stabilizing the actual projective line scales its chosen nonzero vector. -/
theorem lineStabilizer_scales_baseVector (g : lineStabilizer k) :
    ∃ c : k, c ≠ 0 ∧ (naturalAction k g.val).val (baseVector k) = c • baseVector k := by
  have hg : g.val • baseLine k = baseLine k := g.prop
  have h := congrArg Subtype.val hg
  change (naturalAction k g.val).val • Projectivization.mk k (baseVector k) _ =
    Projectivization.mk k (baseVector k) _ at h
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c.val, c.ne_zero, hc.symm⟩

/-- The first pinned root matrix is a Siegel transformation with parameter in
the second hyperbolic summand. -/
theorem positiveSimplePoint_zero_naturalAction_siegel (a : k) :
    naturalAction k (positiveSimplePoint k 0 a) =
      siegelElement (quadraticForm k) (baseVector k) (0, Pi.single 1 a)
        (baseVector_singular k) (by
          rw [hyperbolicForm_polar]
          simp [baseVector, Pi.single_apply]) := by
  rw [naturalAction_rootPoint]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (evenOrthogonalRootIsometry 4 (simpleRoot 0) a) x =
    siegel (quadraticForm k) (baseVector k) (0, Pi.single 1 a) x
  simp only [typeDSimpleRootIndex, show (-1 : ℝ) ≠ 1 by norm_num,
    evenOrthogonalRootIsometry, Fin.val_zero, Nat.zero_lt_succ,
    ↓reduceDIte, hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv]
  change (x.1 + (a * x.1 1) • Pi.single 0 1,
    x.2 - (a * x.2 0) • Pi.single 1 1) =
      siegel (quadraticForm k) (baseVector k) (0, Pi.single 1 a) x
  have hu : (quadraticForm k).polarBilin x (baseVector k) = x.2 0 := by
    rw [hyperbolicForm_polar]
    simp [baseVector, Pi.single_apply]
  have hv : (quadraticForm k).polarBilin x (0, Pi.single 1 a) = a * x.1 1 := by
    rw [hyperbolicForm_polar]
    simp [Pi.single_apply, mul_comm]
  simp only [siegel, hu, hv, quadraticForm, hyperbolicForm_apply,
    Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_smul, sub_zero]
  apply Prod.ext <;> funext i
  · simp [baseVector]
  · simp [baseVector, Pi.single_apply, mul_comm]

/-- Pull back the abelian Siegel subgroup along the actual Spin natural action. -/
def lineSiegelSubgroup : Subgroup (Points k) :=
  (SiegelDirection.subgroup (quadraticForm k) (baseVector k) (baseVector_singular k)).comap
    (naturalAction k)

instance lineSiegelSubgroup_isMulCommutative : IsMulCommutative (lineSiegelSubgroup k) :=
  Subgroup.comap_injective_isMulCommutative _ (naturalAction_injective k)

omit [CharP k 2] in
/-- Normality is relative to the singular-line stabilizer. -/
instance lineSiegelSubgroup_normal_in_stabilizer :
    ((lineSiegelSubgroup k).subgroupOf (lineStabilizer k)).Normal where
  conj_mem r hr g := by
    obtain ⟨c, hc, hg⟩ := lineStabilizer_scales_baseVector k g
    change naturalAction k (g.val * r.val * g.val⁻¹) ∈
      SiegelDirection.subgroup (quadraticForm k) (baseVector k) (baseVector_singular k)
    rw [map_mul, map_mul, map_inv]
    exact SiegelDirection.conj_mem (quadraticForm k) (baseVector k) (baseVector_singular k)
      (naturalAction k g.val) c hc hg (naturalAction k r.val) hr

/-- Every first-root element lies in the pulled-back Siegel subgroup. -/
theorem firstRoot_le_lineSiegelSubgroup :
    rootPointSubgroup k (simpleRoot 0) ≤ lineSiegelSubgroup k := by
  rintro g ⟨a, rfl⟩
  change naturalAction k (positiveSimplePoint k 0 a.toAdd) ∈
    SiegelDirection.subgroup (quadraticForm k) (baseVector k) (baseVector_singular k)
  rw [positiveSimplePoint_zero_naturalAction_siegel]
  exact ⟨Multiplicative.ofAdd ⟨(0, Pi.single 1 a.toAdd), by
    change (quadraticForm k).polarBilin (baseVector k) (0, Pi.single 1 a.toAdd) = 0
    rw [hyperbolicForm_polar]
    simp [baseVector, Pi.single_apply]⟩, rfl⟩

/-- Relative normal closure stays in the Siegel subgroup, since the line
stabilizer normalizes it and it contains the first root group. -/
theorem lineRootClosure_le_lineSiegelSubgroup :
    lineRootClosure k ≤ lineSiegelSubgroup k := by
  have h : stabilizerRootClosure k ≤
      (lineSiegelSubgroup k).subgroupOf (lineStabilizer k) :=
    Subgroup.normalClosure_le_normal (fun _ hx => firstRoot_le_lineSiegelSubgroup k hx)
  rintro g ⟨x, hx, rfl⟩
  exact h hx

/-- The relative root closure in the singular-line stabilizer is abelian. -/
theorem lineRootClosure_isMulCommutative : IsMulCommutative (lineRootClosure k) := by
  apply IsMulCommutative.of_setLike_mul_comm
  intro x hx y hy
  exact setLike_mul_comm (lineRootClosure_le_lineSiegelSubgroup k hx)
    (lineRootClosure_le_lineSiegelSubgroup k hy)

end Triality.SimplyConnected.NormalRootExtraction
