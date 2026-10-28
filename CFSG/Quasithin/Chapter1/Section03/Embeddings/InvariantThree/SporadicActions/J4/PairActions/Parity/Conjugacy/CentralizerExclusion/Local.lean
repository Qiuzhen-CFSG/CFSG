module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.CentralizerExclusion.Linear
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.Alignment
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.Realization.NormalClosure
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel

/-!
# Excluding order 35 in the entire generated max2 subgroup

Let H be the certified max2 subgroup and N its relative seed normal closure.
The proved coordinates on N/⟨t⟩ give a homomorphism from every element of H
into GL₁₂(2). Its generator images are the certified raw column matrices.
The proved basis change and reverse word certificates put the whole image
in the fixed ATLAS linear model; no full-centralizer generation is used.

The normal closure is extraspecial with center ⟨t⟩. An element acting
trivially on N/⟨t⟩ differs from an element of N by one centralizing N.
The proved relative centralizer bound therefore puts the action kernel in
N, a two-group. Order 35 survives the comparison map and is excluded by
`Linear`. The full centralizer still requires the separate generation theorem.

Source motivation: GLS3 Table 5.3i, printed p.270,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. Matrix and word provenance, including
the row-to-column convention, is retained in the imported coordinate and
alignment modules. All their action, kernel and containment inputs used here
are discharged for the actual generated subgroup.
-/

public section

open Subgroup
open scoped Matrix

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.CentralizerExclusion

open Janko4.OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreCentralizerData TwoCoreLinearModel
open TwoCoreComparison (binaryAutMatrix binaryAutMatrix_mulVec)
open TwoCoreComparison.CoordinateGenerators

private noncomputable def rawAction : localSubgroup →* Matrix12ˣ :=
  binaryAutMatrix.toMonoidHom.comp
    (OuterImageComparison.coordinateAction OuterImageComparison.coordinates)

private theorem rawAction_mulVec (g : localSubgroup) (n : localNormalClosure) :
    (rawAction g : Matrix12) *ᵥ
        (OuterImageComparison.coordinates (OuterImageComparison.projection n)).toAdd =
      (OuterImageComparison.coordinates
        (OuterImageComparison.projection (localNormalClosureAction g n))).toAdd := by
  rw [show rawAction g = binaryAutMatrix
    (OuterImageComparison.coordinateAction OuterImageComparison.coordinates g) from rfl,
    binaryAutMatrix_mulVec]
  change (OuterImageComparison.coordinates
    (OuterImageComparison.quotientAction g
      (OuterImageComparison.coordinates.symm
        (OuterImageComparison.coordinates (OuterImageComparison.projection n))))).toAdd = _
  rw [MulEquiv.symm_apply_apply, OuterImageComparison.quotientAction_projection]

private theorem rawAction_eq_of_mulVec (g : localSubgroup) (u : Matrix12ˣ)
    (hu : ∀ n : localNormalClosure,
      (u : Matrix12) *ᵥ
          (OuterImageComparison.coordinates (OuterImageComparison.projection n)).toAdd =
        (OuterImageComparison.coordinates
          (OuterImageComparison.projection (localNormalClosureAction g n))).toAdd) :
    rawAction g = u := by
  apply Units.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  obtain ⟨q, hq⟩ := OuterImageComparison.coordinates.surjective (Multiplicative.ofAdd v)
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective OuterImageComparison.centralPowers q
  have hv : (OuterImageComparison.coordinates (OuterImageComparison.projection n)).toAdd = v :=
    congrArg Multiplicative.toAdd hq
  rw [← hv, rawAction_mulVec, hu]

private theorem rawAction_x : rawAction subgroupX = rawUnitX :=
  rawAction_eq_of_mulVec subgroupX rawUnitX Realization.normalClosure_actionX

private theorem rawAction_y : rawAction subgroupY = rawUnitY :=
  rawAction_eq_of_mulVec subgroupY rawUnitY Realization.normalClosure_actionY

private noncomputable def alignedAction : localSubgroup →* Matrix12ˣ :=
  (MulAut.conj basisUnit).toMonoidHom.comp rawAction

private theorem alignedAction_mem (g : localSubgroup) : alignedAction g ∈ actionGroup := by
  have h : alignedAction.range ≤ actionGroup := by
    rw [MonoidHom.range_eq_map, ← NormalClosureControl.local_generators_generate, MonoidHom.map_closure,
      Set.image_pair]
    apply (Subgroup.closure_le _).mpr
    rintro u (rfl | rfl)
    · change MulAut.conj basisUnit (rawAction subgroupX) ∈ actionGroup
      rw [rawAction_x]
      exact conjugated_rawX_mem
    · change MulAut.conj basisUnit (rawAction subgroupY) ∈ actionGroup
      rw [rawAction_y]
      exact conjugated_rawY_mem
  exact h ⟨g, rfl⟩

/-- The actual quotient action of the generated max2 subgroup, in the certified ATLAS basis. -/
noncomputable def localToLinear : localSubgroup →* actionGroup :=
  alignedAction.codRestrict actionGroup alignedAction_mem

/-- The kernel of the action on N/⟨t⟩ lies in the actual seed normal closure N. -/
theorem quotientAction_ker_le_normalClosure :
    OuterImageComparison.quotientAction.ker ≤ localNormalClosure := by
  intro g hg
  let : IsExtraspecial 2 localNormalClosure := Realization.normalClosure_extraspecial
  have hfix (z : localNormalClosure) (hz : z ∈ center localNormalClosure) :
      localNormalClosureAction g z = z := by
    rw [Realization.normalClosure_center] at hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    rw [map_zpow, OuterImageComparison.action_centralWord]
  have hmod (n : localNormalClosure) (_hn : n ∈ (⊤ : Subgroup localNormalClosure)) :
      localNormalClosureAction g n * n⁻¹ ∈ center localNormalClosure := by
    rw [Realization.normalClosure_center]
    apply (QuotientGroup.eq_one_iff _).mp
    change OuterImageComparison.projection (localNormalClosureAction g n * n⁻¹) = 1
    rw [map_mul, map_inv, ← OuterImageComparison.quotientAction_projection]
    rw [show OuterImageComparison.quotientAction g = 1 from hg]
    exact mul_inv_cancel _
  obtain ⟨r, hr⟩ := extraspecial_two_exists_inner_twist_fixing_subgroup
    (⊤ : Subgroup localNormalClosure) le_top (localNormalClosureAction g) hfix hmod
  have hgr : g * (r : localSubgroup) ∈ localNormalClosureAction.ker := by
    apply MulEquiv.ext
    intro n
    have h := congrArg (fun v : localNormalClosure => (v : localSubgroup))
      (hr n (mem_top n))
    apply Subtype.ext
    change (g * (r : localSubgroup)) * (n : localSubgroup) *
        (g * (r : localSubgroup))⁻¹ = n
    change g * ((r : localSubgroup) * (n : localSubgroup) * (r : localSubgroup)⁻¹) * g⁻¹ = n at h
    simpa only [mul_inv_rev, mul_assoc] using h
  have h := localNormalClosure.mul_mem (localNormalClosureAction_ker_le hgr)
    (localNormalClosure.inv_mem r.property)
  simpa only [mul_inv_cancel_right] using h

/-- Changing coordinates and restricting the codomain preserves the kernel bound. -/
theorem localToLinear_ker_le : localToLinear.ker ≤ localNormalClosure := by
  intro g hg
  apply quotientAction_ker_le_normalClosure
  have h : alignedAction g = 1 := congrArg Subtype.val hg
  change MulAut.conj basisUnit (binaryAutMatrix ((MulAut.congr
    OuterImageComparison.coordinates) (OuterImageComparison.quotientAction g))) = 1 at h
  rw [map_eq_one_iff _ (MulAut.conj basisUnit).injective,
    map_eq_one_iff _ binaryAutMatrix.injective,
    map_eq_one_iff _ (MulAut.congr OuterImageComparison.coordinates).injective] at h
  exact h

/-- The comparison map has a two-group kernel. -/
theorem localToLinear_ker_isPGroup : IsPGroup 2 localToLinear.ker :=
  localNormalClosure_isPGroup.to_le localToLinear_ker_le

/-- Every element of the generated max2 subgroup has order different from 35. -/
theorem localSubgroup_orderOf_ne_thirtyFive (x : localSubgroup) : orderOf x ≠ 35 := by
  intro hx
  exact linear_orderOf_ne_thirtyFive (localToLinear x)
    ((localToLinear.orderOf_map_eq_of_coprime_of_isPGroup_ker
      localToLinear_ker_isPGroup x (by rw [hx]; decide)).trans hx)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.CentralizerExclusion
