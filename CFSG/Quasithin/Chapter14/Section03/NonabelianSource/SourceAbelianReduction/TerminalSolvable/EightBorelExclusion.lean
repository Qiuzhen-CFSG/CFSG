module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.Recognition
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelBinaryTwist
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

/-!
# The original eight-field Borel contradiction, given the marked realization

The actual component and its dotted PSL₂(8) quotient give the original
minimal overgroup K join T. Ambient recognition on its unchanged markings
contradicts the exclusion of Theorem E models. This supplies the eight-field
premise of the existing terminal solvability assembly, without assuming T≤K.

Only the independent earlier construction of MarkedTriality remains explicit.
It is owned by qt-e-1427-eight-amalgam-recognition; no arbitrary completion is
substituted for the original inclusion amalgam.
Source: Aschbacher--Smith 14.3.6(1),14.3.15, pp.991,994
(`refs/quasithin.pdf`).
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Subgroup Theory.GroupTheory
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard
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

/-- The same original component recognizes G, with both endpoint squares
retained. The sole earlier-source input is the actual marked realization. -/
theorem source_eight_marked_ambient_recognition
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    let c := EightLargeParabolic.markedCompletion r
    ∃ f : G ≃* BinaryCarrier 1 Nat.zero_lt_one,
      (∀ x, f (c.left x : G)=ChapterF.SourceCompletion.TrialityTwo.modelCompletion.left x) ∧
      (∀ x, f (c.right x : G)=ChapterF.SourceCompletion.TrialityTwo.modelCompletion.right x) := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact EightLargeParabolic.source_marked_ambient_recognition
    hG hempty hM hu hmany hcard e hH r

/-- The original L₂(8) row is impossible once its genuine marked realization
is supplied. No Borel-placement conclusion or ambient equivalence is assumed. -/
theorem source_eight_marked_false
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (hnot : ¬ClassificationModels.IsTheoremEModel G) : False := by
  obtain ⟨f,_,_⟩ := source_eight_marked_ambient_recognition
    hG T hempty hM hu hmany hcard e hK h8 r
  exact hnot (ClassificationModels.IsTheoremEModel.triality
    ((isTrialityGroupAt_two_iff G).mpr ⟨f⟩))

/-- Discharge the literal eight-field premise of terminal solvability using
the original markings; the catalogue and small-image premises are unchanged. -/
theorem source_terminal_solvable_of_component_inputs_and_markings
    (hnot : ¬ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2) (g : G)
    (hcases : ¬ Group.IsSolvable F.TerminalHdot →
      ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K)
    (hsmall : ∀ K : Subgroup G, ComponentLift F g K → SmallImageRow F K → False)
    (hmarked : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K →
      Nonempty (EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))) :
    Group.IsSolvable F.TerminalHdot := by
  apply source_terminal_solvable_of_component_inputs
    hG T hempty hM hu hmany hcard e hnot F g hcases hsmall
  intro K hK h8
  obtain ⟨r⟩ := hmarked K hK h8
  exact source_eight_marked_false hG T hempty hM hu hmany hcard e hK h8 r hnot

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
