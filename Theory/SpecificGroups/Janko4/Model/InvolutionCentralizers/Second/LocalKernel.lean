module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.MatrixResults
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The elementary kernel in the second J4 seed centralizer

The marked seed lies in the abelian normal kernel of max1. Thus its local
centralizer contains the whole kernel. Restriction preserves normality,
elementary structure, order 2048 and self-centralization. The latter excludes
components by the component/normal-subgroup dichotomy.

Source: Aschbacher--Smith 16.1.5(9), printed p.1172; GLS3 Table 5.3i.
-/

@[expose] public section
namespace Janko4.InvolutionCentralizers.Second
open Subgroup Cardinality LocalStructure Theory.GroupTheory

abbrev Local := max1Subgroup matrixA_mul_self matrixB_pow_four
abbrev seed : Local := localKernelSeed matrixA_mul_self matrixB_pow_four
abbrev localCentralizer : Subgroup Local := centralizer ({seed} : Set Local)
abbrev max1Kernel : Subgroup Local := localKernel matrixA_mul_self matrixB_pow_four

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernelSeed localKernel

/-- The entire elementary kernel commutes with the marked seed. -/
theorem max1Kernel_le_localCentralizer : max1Kernel ≤ localCentralizer := by
  intro n hn
  exact mem_centralizer_singleton_iff.mpr
    (QuotientCount.Image.localKernel_commute _ _ _ hn _ (localKernelSeed_mem _ _))

/-- The embedded kernel inside the actual local centralizer. -/
abbrev kernel : Subgroup localCentralizer := max1Kernel.subgroupOf localCentralizer

instance kernel_normal : kernel.Normal := inferInstance

/-- Restriction to the centralizer retains every original kernel element. -/
noncomputable def kernelEquiv : kernel ≃* max1Kernel :=
  subgroupOfEquivOfLe max1Kernel_le_localCentralizer

/-- The elementary structure is inherited on the actual embedded subgroup. -/
theorem kernel_elementary : IsElementaryAbelian 2 kernel := by
  let := localKernel_elementary matrixA_mul_self matrixB_pow_four
  exact IsElementaryAbelian.subgroupOf max1Kernel_le_localCentralizer

theorem kernel_card : Nat.card kernel = 2048 :=
  (Nat.card_congr kernelEquiv.toEquiv).trans (localKernel_card _ _)

theorem kernel_isTwoGroup : IsPGroup 2 kernel :=
  IsPGroup.of_card (n := 11) kernel_card

/-- Faithfulness of max1's quotient action persists in the seed centralizer. -/
theorem kernel_selfCentralizing : centralizer (kernel : Set localCentralizer) = kernel := by
  apply le_antisymm
  · intro g hg
    change g.val ∈ localKernel matrixA_mul_self matrixB_pow_four
    rw [← centralizer_localKernel matrixA_mul_self matrixB_pow_four]
    intro u hu
    exact congrArg (fun z : localCentralizer => (z : Local))
      (hg ⟨u, max1Kernel_le_localCentralizer hu⟩ hu)
  · intro g hg u hu
    apply Subtype.ext
    exact QuotientCount.Image.localKernel_commute _ _ _ hu _ hg

/-- A component would lie in the elementary kernel, contradicting perfectness. -/
theorem localCentralizer_no_component (K : Subgroup localCentralizer) :
    ¬ IsComponent localCentralizer K := by
  intro hK
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hKQ : K ≤ kernel := by
    rcases hK.normal_dichotomy kernel with hle | hc
    · exact hle
    · exact (commutator_eq_bot_iff_le_centralizer.mp hc).trans kernel_selfCentralizing.le
  let : Group.IsNilpotent K := (kernel_isTwoGroup.to_le hKQ).isNilpotent
  exact Group.IsPerfect.not_isSolvable K inferInstance

end Janko4.InvolutionCentralizers.Second
