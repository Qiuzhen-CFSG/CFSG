module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelCompletion
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.Comparison

/-!
# Triality completion geometry on the literal eight-field component

Apply the genuine whole-overlap, faithful-action and seven-path theorems to
the marked completion extracted from ComponentLift and EightImageRow. The
proved residual calculation identifies K join T with K. Matching endpoint involutions satisfying the hexagon relation in this exact
completion and the native model give its actual triality equivalence.

The independent marked realization remains explicit, owned by
qt-e-1427-eight-amalgam-recognition. Derivation of the Weyl relation from the
ambient centralizer, ambient generation and the terminal Borel exclusion
remain with qt-e-14315-eight-borel-exclusion; no source recognition is claimed.
Source: Aschbacher--Smith 14.2.18--19,14.3.6,14.3.15, pp.987,991,994.
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


/-- The literal component completion has the genuine triality short-path geometry. -/
theorem source_eight_marked_completion_geometry
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    let H := K ⊔ (T : Subgroup G)
    let c := EightLargeParabolic.markedCompletion r
    K = H ∧ Function.Injective (MulAction.toPermHom (H ⊔ EightLargeParabolic.secondParabolic T M Mc H : Subgroup G)
      (ChapterF.SourceCompletion.TrialityTwo.Completion.Vertex c)) ∧
      (∀ v : ChapterF.SourceCompletion.TrialityTwo.Completion.Vertex c,
        SimpleGraph.PathTransitivePolygon.RootPathTransitive
          (ChapterF.SourceCompletion.TrialityTwo.Completion.graph c)
          (H ⊔ EightLargeParabolic.secondParabolic T M Mc H : Subgroup G) v 7) ∧
      (∀ v (p : (ChapterF.SourceCompletion.TrialityTwo.Completion.graph c).Walk v v),
        p.IsCycle → 12 ≤ p.length) := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  exact ⟨hjoin.symm,
    ChapterF.SourceCompletion.TrialityTwo.Completion.vertex_action_injective _,
    ChapterF.SourceCompletion.TrialityTwo.Completion.seven_transitive _,
    ChapterF.SourceCompletion.TrialityTwo.Completion.cycle_length_ge_twelve _⟩

/-- Matching endpoint involutions recognize the generated subgroup on the literal K.
The source derivation of the matching hexagon relation remains with this owner. -/
theorem source_eight_marked_completion_equiv_of_matching_involutions
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (s : _root_.Triality.Standard.Parabolics.parabolic
      ChapterF.SourceCompletion.TrialityTwo.parameters .arms)
    (t : _root_.Triality.Standard.Parabolics.parabolic
      ChapterF.SourceCompletion.TrialityTwo.parameters .central)
    (hs : s^2=1) (ht : t^2=1)
    (hsout : (EightLargeParabolic.markedCompletion r).left s ∉
      (EightLargeParabolic.markedCompletion r).middle.range)
    (htout : (EightLargeParabolic.markedCompletion r).right t ∉
      (EightLargeParabolic.markedCompletion r).middle.range)
    (hbraid : ((EightLargeParabolic.markedCompletion r).left s *
      (EightLargeParabolic.markedCompletion r).right t)^6=1)
    (hmodel : (ChapterF.SourceCompletion.TrialityTwo.modelCompletion.left s *
      ChapterF.SourceCompletion.TrialityTwo.modelCompletion.right t)^6=1) :
    Nonempty ((K ⊔ EightLargeParabolic.secondParabolic T M Mc K : Subgroup G) ≃*
      _root_.Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  obtain ⟨f⟩ := ChapterF.SourceCompletion.TrialityTwo.Completion.nonempty_mulEquiv_of_matching_involutions
    (EightLargeParabolic.markedCompletion r) ChapterF.SourceCompletion.TrialityTwo.modelCompletion
    s t hs ht hsout htout hbraid hmodel
  have hB : K ⊔ EightLargeParabolic.secondParabolic T M Mc K =
      (K ⊔ (T : Subgroup G)) ⊔ EightLargeParabolic.secondParabolic T M Mc (K ⊔ (T : Subgroup G)) := by
    rw [hjoin]
  exact ⟨(MulEquiv.subgroupCongr hB).trans f⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
