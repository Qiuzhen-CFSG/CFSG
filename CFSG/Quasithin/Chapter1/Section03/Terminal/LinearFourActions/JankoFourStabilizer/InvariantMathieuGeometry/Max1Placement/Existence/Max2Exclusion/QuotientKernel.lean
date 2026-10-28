module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientBridge
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientOrder
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound

/-!
# The kernel of the literal max2 quotient action

Transport the published twelve-dimensional row action to the conjugated word
subgroup. Its seed normal closure lies in the kernel. The checked presentation
bounds the quotient by 2661120, while the checked matrix image has at least
2661120 elements. The induced quotient map is therefore injective, identifying
its kernel with that actual normal closure. In particular the original action
has a two-group, hence solvable, kernel.

This concerns the generated max2 subgroup and its relative normal closure.
No equality with the full involution centralizer is required.
Source motivation: GLS3 Table 5.3i, printed p.270. The ATLAS matrix and word
provenance is retained in the imported model modules.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.Max2Exclusion
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound

private theorem sourceEquiv_x : sourceSubgroupEquivLocal sourceX = subgroupX := by
  apply Subtype.ext
  apply centralizerToModel_injective
  exact sourceSubgroupEquivLocal_apply sourceX

private theorem sourceEquiv_y : sourceSubgroupEquivLocal sourceY = subgroupY := by
  apply Subtype.ext
  apply centralizerToModel_injective
  exact sourceSubgroupEquivLocal_apply sourceY

private noncomputable def localMap : localSubgroup →* QuotientMatrixˣ :=
  quotientMap.comp sourceSubgroupEquivLocal.symm.toMonoidHom

private theorem localMap_x : localMap subgroupX = quotientX := by
  rw [← sourceEquiv_x]
  simp [localMap]

private theorem localMap_y : localMap subgroupY = quotientY := by
  rw [← sourceEquiv_y]
  simp [localMap]

private theorem localMap_kills_normalClosure : localNormalClosure ≤ localMap.ker := by
  apply normalClosure_le_normal
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  change localMap ((subgroupX * subgroupY * subgroupX * subgroupY * subgroupY) ^ 11) = 1
  simpa only [map_pow, map_mul, localMap_x, localMap_y] using quotient_seed_eq_one

private theorem ker_eq_of_card_bounds {G H : Type*} [Group G] [Finite G] [Group H]
    (N : Subgroup G) [N.Normal] (f : G →* H) (hN : N ≤ f.ker) {n : ℕ}
    (hupper : Nat.card (G ⧸ N) ≤ n) (hlower : n ≤ Nat.card f.range) : f.ker = N := by
  let g : G ⧸ N →* H := QuotientGroup.lift N f hN
  have he : g.range = f.range := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
      exact ⟨y, rfl⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨QuotientGroup.mk x, rfl⟩
  have hcard : Nat.card (G ⧸ N) ≤ Nat.card g.range := by
    rw [he]
    exact hupper.trans hlower
  have hi := (g.rangeRestrict_surjective.bijective_of_nat_card_le
    hcard).1
  apply le_antisymm _ hN
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply hi
  apply Subtype.ext
  simpa [g] using MonoidHom.mem_ker.mp hx

private theorem localMap_ker : localMap.ker = localNormalClosure := by
  apply ker_eq_of_card_bounds localNormalClosure localMap localMap_kills_normalClosure
    (NormalClosureControl.ActionKernel.Presentation.quotient_card_le_of_presentation_bound
      NormalClosureControl.ActionKernel.Presentation.presentation_finite_card_le)
  apply quotientSubgroup_card_ge.trans
  have hsub : quotientSubgroup ≤ localMap.range := by
    apply (closure_le _).mpr
    rintro x (rfl | rfl)
    · exact ⟨subgroupX, localMap_x⟩
    · exact ⟨subgroupY, localMap_y⟩
  exact Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hsub)

/-- The original action kills exactly the conjugate of the relative seed normal closure. -/
theorem quotientMap_ker_eq : quotientMap.ker =
    localNormalClosure.comap sourceSubgroupEquivLocal.toMonoidHom := by
  ext x
  rw [Subgroup.mem_comap, ← localMap_ker]
  change quotientMap x = 1 ↔
    quotientMap (sourceSubgroupEquivLocal.symm (sourceSubgroupEquivLocal x)) = 1
  rw [MulEquiv.symm_apply_apply]

/-- The original row-quotient action has a two-group kernel. -/
theorem quotientMap_ker_isPGroup : IsPGroup 2 quotientMap.ker := by
  have hlocal : IsPGroup 2 localMap.ker := localMap_ker.symm ▸ localNormalClosure_isPGroup
  let f : quotientMap.ker →* localMap.ker :=
    { toFun := fun x => ⟨sourceSubgroupEquivLocal x, by
        change quotientMap (sourceSubgroupEquivLocal.symm (sourceSubgroupEquivLocal x.val)) = 1
        simpa only [MulEquiv.symm_apply_apply] using MonoidHom.mem_ker.mp x.property⟩
      map_one' := Subtype.ext sourceSubgroupEquivLocal.map_one
      map_mul' := fun x y => Subtype.ext (sourceSubgroupEquivLocal.map_mul x y) }
  exact hlocal.of_injective f (fun x y h =>
    Subtype.ext (sourceSubgroupEquivLocal.injective (congrArg Subtype.val h)))

/-- The kernel required for transporting nonsolvable simple sections is solvable. -/
theorem quotientMap_ker_isSolvable : Group.IsSolvable quotientMap.ker := by
  let : Group.IsNilpotent quotientMap.ker := quotientMap_ker_isPGroup.isNilpotent
  infer_instance

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.Max2Exclusion
