module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourceComplete
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedPairedExclusion

/-!
# Elimination of the original unmarked paired component branch

The direct-sum A₅ branch contradicts original 12.8.13(8). Apply that source
exclusion to the actual component selection, retaining its tensor witness
when the marked component is exchanged. The remaining solvability premises
are the normalized field-four Borel exclusion, the full tensor wreath
quotient, and the separately owned L₂(8) source exclusion.
Source: Aschbacher–Smith 12.8.13(7), 14.3.6 and 14.3.15, pp.856,991–994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

section Source
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hyp

/-- The original source selection is normalized A₅, L₂(8), or an actual
marked tensor on the same selected ambient component. -/
theorem source_normalized_or_tensor
    (hn : ¬ Group.IsSolvable F.TerminalHdot) :
    ∃ K : Subgroup G, ComponentLift F g K ∧
      ((K = conjugateSpanBy K (T : Subgroup G) ∧
        Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 5))) ∨
       EightImageRow F K ∨ Nonempty (ExchangedA5.ActionModel F K)) := by
  rcases source_normalized_or_tensor_or_paired hG T hempty hM hu hmany hcard e hnot
    F hne g hgP hgH hyp hn with h | ⟨L,I,⟨s⟩⟩
  · exact h
  · exact s.false_of_source.elim

/-- Apply the proved paired-source exclusion to the original solvability
consumer. The two A₅ Borel/wreath obligations remain with this owner, and the
L₂(8) obligation with its existing independent producer. -/
theorem source_terminal_solvable_of_borel_wreath_eight
    (hfieldFour : ∀ K : Subgroup G, K ∈ MainForward.localComponents T →
      (T : Subgroup G) ≤ normalizer (K : Set G) →
      (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) → ¬ K ≤ M →
      ¬ (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M)
    (hwreath : ∀ K : Subgroup G, ComponentLift F g K → ExchangedA5.ActionModel F K →
      Nonempty (((conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G)) ≃*
          Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.Wreath))
    (height : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K → False) :
    Group.IsSolvable F.TerminalHdot := by
  exact source_terminal_solvable_of_borel_wreath_paired_eight
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hyp
    hfieldFour hwreath (fun _ _ s => s.false_of_source) height

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
