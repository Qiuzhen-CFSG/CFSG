module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelFullOrder
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.ApartmentReflections

/-!
# Actual endpoint reflections on the literal eight-field component

The exact ambient order, now proved for the original ComponentLift and
EightImageRow, supplies a twelve-cycle and a dihedral reflection subgroup.
The two involutions use the original endpoint maps of the given
MarkedTriality, with product of order six both in the completion and in G.

This constructs a pair satisfying the actual-completion equation.
The native equation must still be established for the same selected pair;
recognition and the original Borel contradiction remain with this owner.
The genuine earlier marked realization remains an explicit premise.
Source: Aschbacher–Smith F.4.15–16,26 and 14.3.6,15, pp.281–282,288,991,994.
-/
public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Subgroup Theory.GroupTheory
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

/-- The actual sixth-power equation and exact product order for an endpoint
pair on the literal component completion, with no extra geometric premise. -/
theorem source_eight_marked_endpoint_involutions
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    let c := EightLargeParabolic.markedCompletion r
    ∃ s : _root_.Triality.Standard.Parabolics.parabolic
        ChapterF.SourceCompletion.TrialityTwo.parameters .arms,
      ∃ t : _root_.Triality.Standard.Parabolics.parabolic
        ChapterF.SourceCompletion.TrialityTwo.parameters .central,
        s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
          (c.left s*c.right t)^6=1 ∧ orderOf (c.left s*c.right t)=6 := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact EightLargeParabolic.source_endpoint_reflection_pair
    hG hempty hM hu hmany hcard e hH r

/-- The same pair satisfies the relation in the original ambient G through
its literal generated-subgroup inclusion. -/
theorem source_eight_ambient_endpoint_involutions
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    let c := EightLargeParabolic.markedCompletion r
    ∃ s : _root_.Triality.Standard.Parabolics.parabolic
        ChapterF.SourceCompletion.TrialityTwo.parameters .arms,
      ∃ t : _root_.Triality.Standard.Parabolics.parabolic
        ChapterF.SourceCompletion.TrialityTwo.parameters .central,
        s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
          ((c.left s : G)*(c.right t : G))^6=1 ∧
            orderOf ((c.left s : G)*(c.right t : G))=6 := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact EightLargeParabolic.source_ambient_endpoint_reflection_pair
    hG hempty hM hu hmany hcard e hH r

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
