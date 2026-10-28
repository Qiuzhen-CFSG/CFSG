module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FullGeometry
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.Reflections

/-!
# Actual hexagon reflections on the original triality markings

The ambient centralizer comparison and original generation theorem give
exactly the native order. Apply the seven-path stabilizer and cycle-reflection
construction to this same marked completion. Its two endpoint preimages are
involutions outside the full common Borel, with product of order six in the
original generated group. Their images in G obey the same equation through
the literal subgroup inclusion.

The native sixth-power equation for this selected pair and ambient
recognition are still open. The independent earlier MarkedTriality input
is retained unchanged.
Source: Aschbacher–Smith F.4.15–16,24,26 and 14.2.18–19, pp.281–282,287–288,987.
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

/-- The original ambient data supply an actual order-six endpoint pair.
The statement retains both maps of the given marked completion. -/
theorem source_endpoint_reflection_pair (r : MarkedTriality T M Mc H) :
    let c := markedCompletion r
    ∃ s : parabolic P .arms, ∃ t : parabolic P .central,
      s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
        (c.left s*c.right t)^6=1 ∧ orderOf (c.left s*c.right t)=6 := by
  apply ChapterF.SourceCompletion.TrialityTwo.Completion.exists_endpoint_involutions_of_order_bound
    (markedCompletion r)
  exact (Nat.card_le_card_of_injective (H ⊔ secondParabolic T M Mc H).subtype
    (H ⊔ secondParabolic T M Mc H).subtype_injective).trans_eq
      (source_card_eq_triality hG hempty hM hu hmany hcard e hH r)

/-- The equation and exact order hold in G under the original inclusion,
for the same two endpoint preimages. -/
theorem source_ambient_endpoint_reflection_pair (r : MarkedTriality T M Mc H) :
    let c := markedCompletion r
    ∃ s : parabolic P .arms, ∃ t : parabolic P .central,
      s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
        ((c.left s : G)*(c.right t : G))^6=1 ∧
          orderOf ((c.left s : G)*(c.right t : G))=6 := by
  obtain ⟨s,t,hs,ht,hsout,htout,hpow,horder⟩ :=
    source_endpoint_reflection_pair hG hempty hM hu hmany hcard e hH r
  refine ⟨s,t,hs,ht,hsout,htout,congrArg Subtype.val hpow,?_⟩
  exact (Subgroup.orderOf_coe ((markedCompletion r).left s*(markedCompletion r).right t)).trans horder

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
