module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.ApartmentReflections
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.CartanReflections

/-!
# Cartan-aligned reflections on the original triality markings

The proved ambient order bounds the original marked completion. Its actual
apartment reflections can be conjugated by one common Borel element so that
both normalize the image of the fixed native torus. Their native preimages
normalize that same torus; the actual product still has order six.

The native sixth-power equation and ambient recognition remain open. The
genuine earlier MarkedTriality input is retained with its literal inclusions.
Source: Aschbacher--Smith F.4.15--17 and14.2.18--19, pp.281--283,987.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
local notation "P" => binaryParameters 1 Nat.zero_lt_one
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hu hmany hcard e hH

/-- A common Borel conjugation chooses the actual order-six pair with both
native preimages normalizing the fixed torus. The given endpoint maps are
unchanged. -/
theorem source_endpoint_torus_reflection_pair (r : MarkedTriality T M Mc H) :
    let c := markedCompletion r
    ∃ s : parabolic P .arms, ∃ t : parabolic P .central,
      s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
        (c.left s*c.right t)^6=1 ∧ orderOf (c.left s*c.right t)=6 ∧
        c.left s ∈ normalizer
          (ChapterF.SourceCompletion.TrialityTwo.Completion.borelTorus.map c.middle : Set _) ∧
        c.right t ∈ normalizer
          (ChapterF.SourceCompletion.TrialityTwo.Completion.borelTorus.map c.middle : Set _) ∧
        ChapterF.SourceCompletion.TrialityTwo.modelCompletion.left s ∈
          normalizer (ConcreteBruhat.torus P : Set (Carrier P)) ∧
        ChapterF.SourceCompletion.TrialityTwo.modelCompletion.right t ∈
          normalizer (ConcreteBruhat.torus P : Set (Carrier P)) := by
  apply ChapterF.SourceCompletion.TrialityTwo.Completion.exists_torus_normalizing_endpoint_involutions_of_order_bound
    (markedCompletion r)
  exact (Nat.card_le_card_of_injective (H ⊔ secondParabolic T M Mc H).subtype
    (H ⊔ secondParabolic T M Mc H).subtype_injective).trans_eq
      (source_card_eq_triality hG hempty hM hu hmany hcard e hH r)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
