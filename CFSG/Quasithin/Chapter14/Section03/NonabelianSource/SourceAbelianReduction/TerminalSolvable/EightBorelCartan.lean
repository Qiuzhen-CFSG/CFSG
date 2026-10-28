module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelApartment
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.CartanReflections

/-!
# A fixed Cartan for the literal eight-row reflection pair

Apply the actual apartment-fixer construction and common Borel conjugation
to the original ComponentLift and EightImageRow. The original ambient
inclusion transports the order-seven torus, normalization by both endpoint
involutions, and the actual sixth-power equation and exact product order.
The same native preimages normalize the fixed native torus.

This supplies the marked common subgroup for the remaining binary
comparison. The native sixth-power relation, recognition and original
Borel contradiction remain with this owner. MarkedTriality is still the
genuine independent earlier premise, not a recognition conclusion.
Source: Aschbacher--Smith F.4.15--17 and14.3.6,15, pp.281--283,991,994.
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

/-- The original component has an actual order-six pair whose native
preimages normalize the fixed torus. All normalization and power equations
use the given marked completion and its literal ambient inclusion. -/
theorem source_eight_marked_torus_endpoint_involutions
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    let c := EightLargeParabolic.markedCompletion r
    let Q := (ChapterF.SourceCompletion.TrialityTwo.Completion.borelTorus.map c.middle).map
      ((K ⊔ (T : Subgroup G)) ⊔ EightLargeParabolic.secondParabolic T M Mc
        (K ⊔ (T : Subgroup G))).subtype
    Nat.card Q = 7 ∧
    ∃ s : _root_.Triality.Standard.Parabolics.parabolic
        ChapterF.SourceCompletion.TrialityTwo.parameters .arms,
      ∃ t : _root_.Triality.Standard.Parabolics.parabolic
        ChapterF.SourceCompletion.TrialityTwo.parameters .central,
        s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
          (c.left s*c.right t)^6=1 ∧ orderOf (c.left s*c.right t)=6 ∧
          ((c.left s : G)*(c.right t : G))^6=1 ∧
          orderOf ((c.left s : G)*(c.right t : G))=6 ∧
          (c.left s : G) ∈ normalizer (Q : Set G) ∧
          (c.right t : G) ∈ normalizer (Q : Set G) ∧
          ChapterF.SourceCompletion.TrialityTwo.modelCompletion.left s ∈ normalizer
            (_root_.Triality.Standard.ConcreteBruhat.torus
              ChapterF.SourceCompletion.TrialityTwo.parameters : Set _) ∧
          ChapterF.SourceCompletion.TrialityTwo.modelCompletion.right t ∈ normalizer
            (_root_.Triality.Standard.ConcreteBruhat.torus
              ChapterF.SourceCompletion.TrialityTwo.parameters : Set _) := by
  constructor
  · rw [card_map_of_injective _root_.Subtype.val_injective,
      card_map_of_injective (EightLargeParabolic.markedCompletion r).middle_injective]
    exact ChapterF.SourceCompletion.TrialityTwo.Completion.borelTorus_card
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  obtain ⟨s,t,hs,ht,hsout,htout,hpow,ho,hsQ,htQ,hsn,htn⟩ :=
    EightLargeParabolic.source_endpoint_torus_reflection_pair
      hG hempty hM hu hmany hcard e hH r
  refine ⟨s,t,hs,ht,hsout,htout,hpow,ho,congrArg Subtype.val hpow,?_,?_,?_,hsn,htn⟩
  · exact (Subgroup.orderOf_coe
      ((EightLargeParabolic.markedCompletion r).left s*
        (EightLargeParabolic.markedCompletion r).right t)).trans ho
  · exact le_normalizer_map _ ⟨_,hsQ,rfl⟩
  · exact le_normalizer_map _ ⟨_,htQ,rfl⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
