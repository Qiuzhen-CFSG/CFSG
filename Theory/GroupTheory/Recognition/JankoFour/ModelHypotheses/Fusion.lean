module

public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Relation0_2

/-!
# A returning conjugate in the concrete J₄ two-core

The certified binary kernel word with mask 6 is conjugate to the first
matrix generator a by an element of Janko4.Model. Quotienting the local
seed normal closure proves that every such kernel word belongs to it.
The certified injectivity of the kernel masks separates mask 6 from
mask 1, whose word is the marked involution. Finally, the established
inclusion-preserving equivalences put this witness in the intrinsic O₂
of the literal centralizer in Model.

This discharges the ambient fusion clause in Aschbacher–Segev's definition
of type J₄, *The study of J₄ via the theory of uniqueness systems* (1992),
p.12, used in Aschbacher–Smith 8.2.14, printed p.723. The existing
`LocalInvolutionCensus.Fusion.Relation0_2` certificate constructs conjugacy
inside Model by an odd-product argument. Its source directory retains the
ATLAS representation, word attribution, and certificate provenance.
-/

public section

open Subgroup
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreCentralizerData LowerBound
open Janko4.Cardinality.LocalInvolutionCensus
open Coordinates FusionCertificates
namespace Janko4.InvolutionCentralizers.First.TypeFusion

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] modelGroup matrixA matrixB sourceSubgroup kernelProduct

private theorem localKernelProduct_mem (i : Fin 8192) :
    localKernelProduct i ∈ localNormalClosure := by
  apply (QuotientGroup.eq_one_iff _).mp
  exact map_kernelProduct_eq_one
    ((QuotientGroup.mk' localNormalClosure).comp sourceSubgroupEquivLocal.toMonoidHom)
    (by
      change QuotientGroup.mk' localNormalClosure (sourceSubgroupEquivLocal sourceSeed) = 1
      rw [sourceEquiv_seed]
      exact (QuotientGroup.eq_one_iff _).mpr localSeed_mem_normalClosure) i

/-- The certified mask-6 word, retained inside the actual local normal closure. -/
noncomputable def returningWord : localNormalClosure :=
  ⟨localKernelProduct 6, localKernelProduct_mem 6⟩

/-- Conjugacy is in the original matrix group, not in the surrounding GL. -/
theorem returningWord_isConj : IsConj Janko4.a (eH returningWord.val) :=
  @transport Janko4.a (kernelProduct 6) (@fuse_0_2 (kernelProduct 6 : Model) eval_kernel_6)

private theorem kernelProduct_one : kernelProduct 1 = sourceSeed ^ 2 := by
  apply Subtype.ext
  apply toMatrix_injective
  change toMatrix (kernelProduct 1 : Model) = toMatrix (kernelFactor 0 : Model)
  rw [eval_kernel_1, KernelSeparation.eval_factor]

/-- The existing distinct-mask certificate separates this word from a. -/
theorem returningWord_ne : eH returningWord.val ≠ Janko4.a := by
  intro he
  have he' : localKernelProduct 6 = zH := eH_injective he
  rw [← sourceEquiv_seed_sq] at he'
  have hk : kernelProduct 6 = kernelProduct 1 :=
    (sourceSubgroupEquivLocal.injective he').trans kernelProduct_one.symm
  have hf := kernelProduct_injective hk
  exact (by decide : (6 : Fin 8192) ≠ 1) hf

/-- Transport to the intrinsic two-core of the literal centralizer in Model. -/
noncomputable def returningCoreElement : pCore 2 centralizer :=
  twoCoreEquiv.symm (normalClosureEquivTwoCore returningWord)

/-- The transport retains the actual element of the original group. -/
theorem returningCoreElement_coe :
    ((returningCoreElement : centralizer) : Model) = eH returningWord.val := by
  apply toAmbient_injective
  rw [← centralizerEquiv_coe, ← twoCoreEquiv_coe]
  change ((twoCoreEquiv (twoCoreEquiv.symm (normalClosureEquivTwoCore returningWord)) :
    involutionCentralizer) : BinaryMatrixˣ) = _
  rw [twoCoreEquiv.apply_symm_apply, normalClosureEquivTwoCore_coe]
  rfl

/-- A genuine distinct returning conjugate, with membership in the actual two-core. -/
theorem exists_returning_twoCore :
    ∃ q : pCore 2 centralizer, IsConj a ((q : centralizer) : Model) ∧
      ((q : centralizer) : Model) ≠ a := by
  refine ⟨returningCoreElement, ?_, ?_⟩
  · rw [returningCoreElement_coe]
    exact returningWord_isConj
  · rw [returningCoreElement_coe]
    exact returningWord_ne

end Janko4.InvolutionCentralizers.First.TypeFusion
