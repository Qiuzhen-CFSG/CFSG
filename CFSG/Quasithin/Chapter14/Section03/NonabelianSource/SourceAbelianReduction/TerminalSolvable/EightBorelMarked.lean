module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelSource
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.Completion
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelKernel

/-!
# The marked eight-field source on the terminal component

The proved dotted-kernel comparison supplies the actual K/O₂(K) equivalence.
Borel placement and minimality then put H = K join T in the exact earlier
large-parabolic problem, with embedded O²(H) = K. An explicit marked triality
isomorphism yields the original Sylow order, extraspecial first core, central
involution marking, literal centralizer, and faithful completion with whole
overlap H intersection M.

The final two reductions connect earlier large-parabolic classification to the
literal eight-row contradiction and terminal solvability. That classification,
including the cubic-extension and ambient-recognition arguments, remains with
qt-e-14315-eight-borel-exclusion. The independent marked realization remains with
qt-e-1427-eight-amalgam-recognition; catalogue and small-image assembly stay with
qt-e-14315-terminal-solvable. These are conditional reductions, not completed
source 14.2.19 or 14.3.15.

Source: Aschbacher--Smith 14.2.16--19,14.3.6(1),14.3.15,
printed pp.986--987,991,994 (`refs/quasithin.pdf`).
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

/-- The completed kernel comparison gives the intrinsic quotient used by 14.3.6. -/
def eightIntrinsicQuotientEquiv (hK : ComponentLift F g K) (h8 : EightImageRow F K) :
    (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3 :=
  (componentCoreQuotientEquivDot F hK.le_pointNormalizer
    (componentDotMap_ker_eq_twoCore_of_eight hG F hK h8)).trans (Classical.choice h8.2)

include hG hempty hM hu hmany hcard e

/-- The actual 14.3.15 join is a minimal outside parabolic and its embedded
O² is exactly K. Its residual quotient is obtained from the proved dotted kernel. -/
theorem source_eight_join_minimal (hK : ComponentLift F g K) (h8 : EightImageRow F K) :
    K ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) M ∧
      EightLargeParabolic.residual (K ⊔ (T : Subgroup G)) = K ∧
      Nonempty (((pResidual 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ⧸
        pCore 2 (pResidual 2 (K ⊔ (T : Subgroup G) : Subgroup G))) ≃*
          Theory.PSL2.BinaryGroup 3) := by
  let eK := eightIntrinsicQuotientEquiv hG T hK h8
  have hout := hK.not_le hM.1.2 e
  have hn := (eight_join_source_applicability hK h8 hout).1
  have hB := (source_eight_borel_placement hG T hempty hM hu hmany hcard e K hn eK).trans inf_le_left
  exact ⟨eight_join_mem_HStar_of_borel_le hM.1.2 hK h8 hout eK hB,
    (eight_join_source_applicability hK h8 hout).2.2.2,
    eight_join_residual_quotient hK h8 hout eK⟩

/-- Local 14.2.16--18 consequences on the literal terminal component join.
The marked realization remains the independent earlier input; no containment
of T in K or equality of H and Mc is assumed. -/
theorem source_eight_marked_local_consequences
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    let H := K ⊔ (T : Subgroup G)
    IsExtraspecial 2 (H.pCoreIn 2) ∧ Nat.card (H.pCoreIn 2) = 512 ∧
      EightLargeParabolic.firstCoreCenter H = centralInvolutions T ∧
      (∀ z : G, z ∈ centralInvolutions T → z ≠ 1 → Mc = centralizer ({z} : Set G)) ∧
      normalizer (H.pCoreIn 2 : Set G) ≤ Mc ∧ Mc.pCoreIn 2 ≤ H.pCoreIn 2 ∧
      Nat.card T = 4096 ∧
      (EightLargeParabolic.markedCompletion r).middle.range.map
        (H ⊔ EightLargeParabolic.secondParabolic T M Mc H).subtype = H ⊓ M ∧
      (EightLargeParabolic.markedCompletion r).middle.range.normalCore = ⊥ := by
  obtain ⟨hH, _, ⟨eR⟩⟩ := source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8
  exact ⟨EightLargeParabolic.firstCore_extraspecial r,
    EightLargeParabolic.firstCore_card r,
    EightLargeParabolic.source_firstCore_center hG hempty hM hu hmany hcard e hH r,
    fun _ hz hn => EightLargeParabolic.source_partner_eq_element_centralizer
      hG hempty hM hu hmany hcard e hH r hz hn,
    EightLargeParabolic.source_firstCore_normalizer_le hG hempty hM hu hmany hcard e hH r,
    EightLargeParabolic.source_partner_core_le hG hempty hM hu hmany hcard e hH,
    EightLargeParabolic.source_sylow_card r hH.1.1.2,
    (EightLargeParabolic.markedCompletion_middle_image r).trans
      (EightLargeParabolic.source_parabolics hG T hempty hM hu hmany hcard e _ hH eR).2.2.2.1,
    EightLargeParabolic.source_markedCompletion_corefree hG hempty hM hu hmany hcard e hH eR r⟩

/-- Once this task's earlier large-parabolic recognition is proved, the literal
eight-row exclusion follows without a kernel or applicability callback. -/
theorem source_eight_exclusion_of_large_parabolics
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (hlarge : ∀ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) M →
      Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃*
        Theory.PSL2.BinaryGroup 3) → ClassificationModels.IsTheoremEModel G)
    (hK : ComponentLift F g K) (h8 : EightImageRow F K) : False := by
  obtain ⟨hH, _, hquot⟩ := source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8
  exact hnot (hlarge _ hH hquot)

/-- Literal terminal solvability, conditional only on the other image rows and
this task's earlier large-parabolic classification. The terminal-solvability
assembly owner discharges the catalogue and small-image inputs. -/
theorem source_terminal_solvable_of_eight_large_parabolics
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (hlarge : ∀ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) M →
      Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃*
        Theory.PSL2.BinaryGroup 3) → ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2) (g : G)
    (hcases : ¬ Group.IsSolvable F.TerminalHdot →
      ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K)
    (hsmall : ∀ K : Subgroup G, ComponentLift F g K → SmallImageRow F K → False) :
    Group.IsSolvable F.TerminalHdot := by
  apply source_terminal_solvable_of_component_inputs
    hG T hempty hM hu hmany hcard e hnot F g hcases hsmall
  intro K hK h8
  exact source_eight_exclusion_of_large_parabolics
    hG T hempty hM hu hmany hcard e hnot hlarge hK h8

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
