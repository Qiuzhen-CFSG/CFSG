module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.FirstSwaps
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.MixedPairs.GeneratorY

/-! Exact forward residual characters for the remaining mixed census pairs.
The full first-centralizer residual has index two. The original generator Y
has cube one and hence lies in it; generation then forces X outside it.
Source: Kleidman--Wilson (1988), p.487, Corollary 1.1.4. -/

public noncomputable section
open Subgroup Theory.GroupTheory
open Janko4.Cardinality.LocalInvolutionCensus
namespace Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound Coordinates FusionCertificates
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private def sourceCentralizerEquiv : sourceSubgroup ≃* InvolutionCentralizers.First.centralizer :=
  sourceSubgroupEquivLocal.trans Janko4.Cardinality.Thompson.max2EquivCentralizer

private def sourceHalf : Subgroup sourceSubgroup :=
  (solvableResidual InvolutionCentralizers.First.centralizer).comap
    sourceCentralizerEquiv.toMonoidHom

private theorem sourceHalf_index : sourceHalf.index = 2 := by
  rw [sourceHalf, index_comap_of_surjective _ sourceCentralizerEquiv.surjective]
  exact first_residual_index

/-- The original word subgroup uses precisely the intrinsic residual character. -/
theorem innerRelated_source_iff_first (u : sourceSubgroup) :
    InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model) (u : Model) ↔
      InnerRelated Janko4.a (eH (sourceSubgroupEquivLocal u)) := by
  have hs : (MulAut.conj h⁻¹) ((sourceSeed ^ 2 : sourceSubgroup) : Model) = Janko4.a := by
    simpa only [MulAut.conj_apply, inv_inv, coe_sourceSeed_sq] using conjugates_t
  have hu : (MulAut.conj h⁻¹) (u : Model) = eH (sourceSubgroupEquivLocal u) := by
    rw [eH_sourceSubgroupEquivLocal, MulAut.conj_apply, inv_inv]
  exact (innerRelated_equiv (MulAut.conj h⁻¹) _ _).symm.trans (by rw [hs, hu])

private theorem sourceHalf_mem (u : sourceSubgroup) :
    u ∈ sourceHalf ↔ InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model) (u : Model) := by
  rw [innerRelated_source_iff_first]
  have he : (sourceCentralizerEquiv u : Model) = eH (sourceSubgroupEquivLocal u) :=
    Janko4.Cardinality.Thompson.max2EquivCentralizer_coe _
  rw [← he]
  change sourceCentralizerEquiv u ∈ solvableResidual InvolutionCentralizers.First.centralizer ↔
    InvolutionCentralizers.First.centralizer.subtype (sourceCentralizerEquiv u) ∈
      (solvableResidual InvolutionCentralizers.First.centralizer).map
        InvolutionCentralizers.First.centralizer.subtype
  exact (mem_map_iff_mem (f := InvolutionCentralizers.First.centralizer.subtype)
    InvolutionCentralizers.First.centralizer.subtype_injective).symm

private theorem sourceY_mem_half : sourceY ∈ sourceHalf := by
  have hy : sourceY ^ 3 = 1 := Subtype.ext MixedPairs.w14_cube
  have h2 := sourceHalf.sq_mem_of_index_two sourceHalf_index sourceY
  apply (sourceHalf.mul_mem_cancel_left h2).mp
  simpa only [← pow_succ, hy] using sourceHalf.one_mem

private theorem sourceX_not_mem_half : sourceX ∉ sourceHalf := by
  intro hx
  have ht : sourceHalf = ⊤ := by
    apply top_unique
    rw [← source_generators_generate]
    apply (closure_le _).mpr
    rintro x (rfl | rfl)
    · exact hx
    · exact sourceY_mem_half
  have hi := sourceHalf_index
  rw [ht, index_top] at hi
  omega

private theorem source_pair4_not_inner :
    ¬ InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model) (sourceRepresentative 4) := by
  rw [← sourceHalf_mem]
  have hk : kernelProduct 0 = 1 := by simp [kernelProduct]
  change kernelProduct 0 * sourceX ∉ sourceHalf
  rw [hk, one_mul]
  exact sourceX_not_mem_half

private theorem source_pair6_not_inner :
    ¬ InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model) (sourceRepresentative 6) := by
  rw [← sourceHalf_mem]
  have hk : kernelProduct 1 ∈ sourceHalf := (sourceHalf_mem _).mpr (innerRelated_source_kernel 1)
  change kernelProduct 1 * (sourceX * sourceY) ^ 7 ∉ sourceHalf
  rw [sourceHalf.mul_mem_cancel_left hk]
  have h6 := sourceHalf.pow_mem (sourceHalf.sq_mem_of_index_two sourceHalf_index
    (sourceX * sourceY)) 3
  rw [show (7 : ℕ) = 2 * 3 + 1 from rfl, pow_succ, pow_mul,
    sourceHalf.mul_mem_cancel_left h6, sourceHalf.mul_mem_cancel_right sourceY_mem_half]
  exact sourceX_not_mem_half

private theorem source_pair8_inner :
    InnerRelated ((sourceSeed ^ 2 : sourceSubgroup) : Model) (sourceRepresentative 8) := by
  rw [← sourceHalf_mem]
  change kernelProduct 12 * ((sourceX * sourceY) ^ 5 * sourceY) ^ 4 ∈ sourceHalf
  apply sourceHalf.mul_mem ((sourceHalf_mem _).mpr (innerRelated_source_kernel 12))
  simpa only [← pow_mul] using sourceHalf.pow_mem
    (sourceHalf.sq_mem_of_index_two sourceHalf_index (((sourceX * sourceY) ^ 5 * sourceY))) 2

/-- The fourth representative is in the actual outer half. -/
theorem first_pair4_not_forward : ¬ InnerRelated Janko4.a (eH (representative 4)) := by
  rw [representative_eq, ← innerRelated_source_iff_first]
  exact source_pair4_not_inner

/-- The sixth representative is in the actual outer half. -/
theorem first_pair6_not_forward : ¬ InnerRelated Janko4.a (eH (representative 6)) := by
  rw [representative_eq, ← innerRelated_source_iff_first]
  exact source_pair6_not_inner

/-- The eighth representative is in the actual inner half. -/
theorem first_pair8_forward : InnerRelated Janko4.a (eH (representative 8)) := by
  rw [representative_eq, ← innerRelated_source_iff_first]
  exact source_pair8_inner

end Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
