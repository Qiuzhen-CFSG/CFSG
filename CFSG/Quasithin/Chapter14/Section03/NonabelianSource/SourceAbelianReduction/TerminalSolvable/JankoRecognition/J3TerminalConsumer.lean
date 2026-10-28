module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Source
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelExclusion

/-!
# J₃ terminal-solvability consumer

This leaf connects the conditional J₃ recognition source to the actual marked
L₂(8) terminal consumer.  The Thompson--Higman--McKay inputs remain literal
arguments: the finite presentation, its order bound, the order-243 subgroup,
and the injective `L₂(16):2` map.  The marked-triality witness is likewise
retained as an independent premise.  No family tag or unmarked eight-row
record is used as a substitute.

Source: Aschbacher--Smith I.4.7(2), 14.3.6(1), and 14.3.15, printed
pp.418, 991, and 994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

namespace JankoRecognition

/-- The original terminal solvability endpoint with both independent source
    contracts assembled at their literal consumers. -/
theorem source_terminal_solvable_of_j3_linear_extension_marked
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hgen : Sporadic.Janko3.RecognitionPresentation.HasGenerators G)
    (hfinite : Finite Sporadic.Janko3.RecognitionPresentation.Presentation)
    (hbound : Nat.card Sporadic.Janko3.RecognitionPresentation.Presentation ≤ 50232960)
    (P : Subgroup G) (hP : Nat.card P = 243)
    (f : Theory.PSL2.BinaryFourFieldExtension.Model →* G)
    (hf : Function.Injective f)
    (hmarked : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K →
      Nonempty (EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))) :
    Group.IsSolvable F.TerminalHdot := by
  apply source_terminal_solvable_of_j3_linear_extension_eight_exclusion
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH
    hgen hfinite hbound P hP f hf
  intro K hK h8
  obtain ⟨r⟩ := hmarked K hK h8
  exact source_eight_marked_false hG T hempty hM hu hmany hcard e hK h8 r hnot

end JankoRecognition

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
