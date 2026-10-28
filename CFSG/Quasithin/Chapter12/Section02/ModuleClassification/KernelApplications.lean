module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.KernelEquality
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.NonbinaryApplication

/-!
# Original kernels in the nonbinary source application

Faithfulness of the action of L/O2(L) on the actual central quotient
identifies both the relative centralizer and the original central-action
kernel with O2(L). The nonbinary rows constructed from B.5 therefore carry
these identities, including the SL3(4) case; no simplicity assumption on
the original quasisimple actor is made.
Source: Aschbacher--Smith 11.0.1 and 12.2.2, pp.759--760,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

theorem centralKernel_eq_twoCore_of_injective
    (hf : Function.Injective D.centralQuotientAction) :
    D.chosenCentralAction.ker = pCore 2 L := by
  apply le_antisymm _ D.centralAction_core
  intro l hl
  apply (QuotientGroup.eq_one_iff l).mp
  apply hf
  exact hl.trans (map_one D.centralQuotientAction).symm

theorem actionCentralizer_eq_twoCore_of_injective
    (hf : Function.Injective D.centralQuotientAction) :
    (centralizer (V : Set G)).subgroupOf L = pCore 2 L := by
  apply le_antisymm
  · exact D.actionCentralizer_le_centralAction_ker.trans_eq
      (D.centralKernel_eq_twoCore_of_injective hf)
  · exact D.chosenAction_core.trans D.chosenAction_ker.le

/-- The precise input consumed by Chapter 11 has the original kernels,
not merely an isomorphism of abstract central quotients. -/
theorem nonbinaryInput_kernels (a : D.NonbinaryNaturalInput) :
    (centralizer (V : Set G)).subgroupOf L = pCore 2 L ∧
      D.chosenCentralAction.ker = pCore 2 L :=
  ⟨D.actionCentralizer_eq_twoCore_of_injective a.faithful,
    D.centralKernel_eq_twoCore_of_injective a.faithful⟩

namespace LiteralComparison
open ChapterB.QuasisimpleSource
variable {D} {H : Type*} [Group H]
    {ρ : Representation (ZMod 2) H D.space} {K : Subgroup H}
    (c : D.LiteralComparison ρ K)
include c

/-- Actual nonbinary row application, retaining the field/action witness,
T-invariance, the multiple-overgroup guard and both original kernel identities. -/
theorem nonbinaryInput_with_kernels_of_source_branch
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (horbits : componentOrbit V (normalizer (L : Set G)) = V ∨
      (componentOrbit V (T : Subgroup G) = V ∧ V ⊓ centralizer (L : Set G) = ⊥))
    (hff : IsFFModule (normalizerRepresentation D.chosenAction))
    (s : MovedSection ρ K) (hf : Function.Injective (s.action.comp K.subtype))
    (F : BinaryField) (hF : 1 < F.degree) (row : NonbinaryRow s F) :
    Nonempty D.NonbinaryNaturalInput ∧
      (centralizer (V : Set G)).subgroupOf L = pCore 2 L ∧
      D.chosenCentralAction.ker = pCore 2 L := by
  obtain ⟨a⟩ := c.nonbinaryInput_of_source_branch h hmany horbits hff s hf F hF row
  exact ⟨⟨a⟩,D.nonbinaryInput_kernels a⟩

end LiteralComparison
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
