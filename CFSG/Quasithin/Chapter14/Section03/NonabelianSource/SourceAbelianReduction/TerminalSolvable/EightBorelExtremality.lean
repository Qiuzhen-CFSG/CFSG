module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelShortCentralizer
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.ShortUniqueFixed

/-!
# Extremality and full endpoint fusion on the original L₂(8) component

Apply the ambient Sylow-centralizer and involution-fusion results to the
literal K join T supplied by ComponentLift and EightImageRow. The original
central involution and the short root pulled back through the original
right marking represent the two distinct ambient involution classes.
In the Mc = K join T branch, the commuting-class count gives unique fixed
cosets in the actual short centralizer and determines the four-plane's
normalizer there. No replacement amalgam or ambient recognition is assumed.

These discharge the extremality and endpoint-fusion inputs preceding
Aschbacher--Smith F.4.42, printed pp.294--295, in 14.2.18--19 and 14.3.15,
printed pp.987,994. The full ambient short-centralizer comparison,
matching sixth-power equations, ambient generation/recognition and Borel
contradiction remain with this source family. The marked realization
remains explicit and must be discharged by its independent producer.
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

/-- Literal F.4.40 on the original eight-field lift: the selected short-root
centralizer has exactly the original Sylow intersection as a Sylow subgroup. -/
theorem source_eight_marked_short_extremal
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (a : _root_.Triality.Standard.ExtensionField
      (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one)) (ha : a ≠ 0) :
    let t := (EightLargeParabolic.markedShortRoot r a : G)
    ∃ S : Sylow 2 (centralizer ({t} : Set G)),
      (S : Subgroup (centralizer ({t} : Set G))) =
        (T : Subgroup G).subgroupOf (centralizer ({t} : Set G)) := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact EightLargeParabolic.source_short_ambient_sylow hG hempty hM hu hmany hcard e hH r a ha

/-- The original two endpoint maps preserve and reflect ambient involution
fusion, as required for the commuting-class comparison in F.4.42. -/
theorem source_eight_marked_endpoint_involution_fusion_iff
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (x : (K ⊔ (T : Subgroup G) : Subgroup G))
    (y : EightLargeParabolic.secondParabolic T M Mc (K ⊔ (T : Subgroup G)))
    (hx : orderOf (x : G) = 2) (hy : orderOf (y : G) = 2) :
    IsConj (x : G) (y : G) ↔ IsConj (r.left x).val (r.right y).val := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact EightLargeParabolic.source_first_second_fusion_iff hG hempty hM hu hmany hcard e hH r x y hx hy

/-- The two original marked involutions represent all ambient involution
classes, and are not fused, including when Mc has a cubic supplement. -/
theorem source_eight_marked_two_involution_classes
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (a : _root_.Triality.Standard.ExtensionField
      (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one)) (ha : a ≠ 0)
    {z : G} (hz : z ∈ centralInvolutions T) (hz1 : z ≠ 1) :
    ¬ IsConj z (EightLargeParabolic.markedShortRoot r a : G) ∧
      ∀ x : G, orderOf x = 2 →
        IsConj z x ∨ IsConj (EightLargeParabolic.markedShortRoot r a : G) x := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact ⟨EightLargeParabolic.source_short_not_conj_center hG hempty hM hu hmany hcard e hH r a ha hz hz1,
    EightLargeParabolic.source_involution_classes hG hempty hM hu hmany hcard e hH r a ha hz hz1⟩

/-- In the Mc = K join T branch, the original commuting-class count gives
unique cosets in the full ambient short centralizer. -/
theorem source_eight_marked_short_unique_fixed_of_partner_eq
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (hplain : Mc = K ⊔ (T : Subgroup G))
    (a : _root_.Triality.Standard.ExtensionField
      (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one)) (ha : a ≠ 0)
    {z : G} (hz : z ∈ centralInvolutions T) (hz1 : z ≠ 1) :
    let C := centralizer ({(EightLargeParabolic.markedShortRoot r a : G)} : Set G)
    ∀ x : C, IsConj z (x : G) →
      ∃! q : C ⧸ (EightLargeParabolic.secondParabolic T M Mc
        (K ⊔ (T : Subgroup G))).subgroupOf C, x • q = q := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact EightLargeParabolic.source_short_unique_fixed_of_partner_eq
    hG hempty hM hu hmany hcard e hH r hplain a ha hz hz1

/-- The four-plane's normalizer in the actual short centralizer is exactly
its original local short centralizer, in the Mc = K join T branch. -/
theorem source_eight_marked_short_plane_normalizer_of_partner_eq
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (hplain : Mc = K ⊔ (T : Subgroup G))
    (a : _root_.Triality.Standard.ExtensionField
      (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one)) (ha : a ≠ 0) :
    let L := EightLargeParabolic.secondParabolic T M Mc (K ⊔ (T : Subgroup G))
    let D := centralizer ({EightLargeParabolic.markedShortRoot r a} : Set L)
    let C := centralizer ({(EightLargeParabolic.markedShortRoot r a : G)} : Set G)
    let f := L.subtype.comp D.subtype
    normalizer ((EightLargeParabolic.markedShortPlane r a ha).map f : Set G) ⊓ C =
      L ⊓ C := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact EightLargeParabolic.source_short_plane_normalizer_of_partner_eq
    hG hempty hM hu hmany hcard e hH r hplain a ha

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
