module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelComponent
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FieldAction

/-!
# The literal eight-row rank-one action and its remaining odd kernel

Apply the original partner action to H = K join T, then use the checked
residual/perfectness comparison H = K. This preserves the actual
ComponentLift, its dotted PSL₂(8) row, both ambient quotient maps and the
original Sylow normalizer. The rank-one kernel lies in M intersect Mc,
meets K in O₂(K), and is odd modulo the partner core. Modulo this actual
kernel the partner is PSL₂(8) or its automorphism group.

The remaining linear-centralizer argument must eliminate that odd kernel
before constructing the cubic extension and applying ambient recognition.
This module does not claim the terminal contradiction. Original 14.2.18--19
and 14.3.15 assembly remains with qt-e-14315-eight-borel-exclusion; the
independent marked realization remains explicit.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    {F : InvariantFlag T (rankTwoSeed T M) 2} {g : G} {K : Subgroup G}
include hG hempty hM hu hmany hcard e

/-- Placement of the actual quotient-action kernel, with the original K and T. -/
theorem source_eight_marked_rankOne_kernel_geometry
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    pCoreActionKernelIn 2 K Mc ≤ normalizer (T : Set G) ∧
      pCoreActionKernelIn 2 K Mc ≤ M ⊓ Mc ∧
      pCoreActionKernelIn 2 K Mc ⊓ K = K.pCoreIn 2 := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have hp := EightLargeParabolic.source_rankOneAction_kernel_placement
    hG hempty hM hu hmany hcard e hH
  have hi := EightLargeParabolic.source_rankOneAction_kernel_inf_first
    hG hempty hM hu hmany hcard e hH r
  simpa only [hjoin] using And.intro hp.1 (And.intro hp.2 hi)

/-- The actual component quotient action, its odd kernel remainder, and both
possible faithful quotient models, all on the original partner Mc. -/
theorem source_eight_marked_rankOne_action
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    ∃ (hn : Mc ≤ normalizer (K : Set G))
      (b : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
      (a : Mc →* MulAut (Theory.PSL2.BinaryGroup 3)),
      (∀ (x : Mc) (k : K), a x (b (QuotientGroup.mk' (pCore 2 K) k)) =
        b (QuotientGroup.mk' (pCore 2 K) (K.normalizerMonoidHom (inclusion hn x) k))) ∧
      a.ker.map Mc.subtype = pCoreActionKernelIn 2 K Mc ∧
      pCore 2 a.ker = (pCore 2 Mc).subgroupOf a.ker ∧
      Odd (Nat.card (a.ker ⧸ (pCore 2 Mc).subgroupOf a.ker)) ∧
      (Nonempty ((Mc ⧸ a.ker) ≃* Theory.PSL2.BinaryGroup 3) ∨
        Nonempty ((Mc ⧸ a.ker) ≃* MulAut (Theory.PSL2.BinaryGroup 3))) := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH : K ∈ Chapter3.HStar (T : Subgroup G) M := by
    simpa only [hjoin] using
      (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have rK : EightLargeParabolic.MarkedTriality T M Mc K := hjoin ▸ r
  refine ⟨EightLargeParabolic.source_partner_le_first_normalizer
      hG hempty hM hu hmany hcard e hH rK, EightLargeParabolic.firstQuotientEquiv rK,
    EightLargeParabolic.sourceRankOneAction hG hempty hM hu hmany hcard e hH rK,
    EightLargeParabolic.source_rankOneAction_mk hG hempty hM hu hmany hcard e hH rK,
    EightLargeParabolic.source_rankOneAction_kernel_map hG hempty hM hu hmany hcard e hH rK,
    ?_,?_,EightLargeParabolic.source_rankOneAction_quotient hG hempty hM hu hmany hcard e hH rK⟩
  · exact (EightLargeParabolic.source_rankOneAction_kernel_core_and_odd
      hG hempty hM hu hmany hcard e hH rK).1
  · exact (EightLargeParabolic.source_rankOneAction_kernel_core_and_odd
      hG hempty hM hu hmany hcard e hH rK).2

/-- The remaining actual core-action centralizer identity feeds the original
partner quotient. Its discharge and the subsequent cubic/ambient assembly
remain with this same source-family owner. -/
theorem source_eight_partner_quotient_of_core_centralizer
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (hc : centralizer ((EightLargeParabolic.firstCoreAction hG hempty hM hu hmany hcard e
      (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1).range :
        Set (MulAut (EightLargeParabolic.PartnerCoreModule Mc))) = ⊥) :
    Nonempty ((Mc ⧸ pCore 2 Mc) ≃* Theory.PSL2.BinaryGroup 3) ∨
      Nonempty ((Mc ⧸ pCore 2 Mc) ≃* MulAut (Theory.PSL2.BinaryGroup 3)) :=
  EightLargeParabolic.source_partner_quotient_of_core_centralizer
    hG hempty hM hu hmany hcard e
    (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1 r hc

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
