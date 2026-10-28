module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.ShortCentralizer
public import Theory.SpecificGroups.Triality.ShortRootCentralizer.Action

/-!
# The original central involution generates the short-centralizer plane

The two endpoint squares send the nonidentity original core-center element
onto the pinned highest long root. Native root conjugators lie in the full
short centralizer, so the local centralizer equivalence transports them to
the original group. Consequently all three nonidentity plane elements form
one local orbit and the plane is exactly the local normal closure of the
original central involution.

This identifies the literal V in the nonunitary part of Aschbacher--Smith
F.4.42, printed p.295, applied at 14.2.18--19 and 14.3.15, pp.987,994.
The orbit assertion supplies a local input; ambient unique fixed cosets,
full short-centralizer containment and recognition remain to be proved.
The original component application is EightBorelShortCentralizer.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.RadicalCoordinates
open _root_.Triality.Standard.RadicalCoordinates.Centers
open _root_.Triality.Standard.RadicalCoordinates.LeviCommutators
open _root_.Triality.Standard.ShortRootCentralizer
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "hp2" => binaryParameters_prime 1 Nat.zero_lt_one
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}

private theorem highest_long_mem : long P hp2 2 1 ∈ highestRoot P := by
  refine ⟨longElementary P hp2 2 1,?_,rfl⟩
  change elementaryInclusion P (longElementary P hp2 2 1) ∈ splitHighestRoot P
  rw [longElementary_val]
  exact ⟨Multiplicative.ofAdd (1 : fixedField P).val,rfl⟩

private theorem highest_long_ne_one : long P hp2 2 1 ≠ 1 := by
  intro he
  have hh := long_two_injective P hp2 (he.trans (long_zero P hp2 2).symm)
  exact one_ne_zero hh

omit [Finite G] in
private theorem marked_center_image (r : MarkedTriality T M Mc H)
    (hTH : (T : Subgroup G) ≤ H) {z : G}
    (hz : z ∈ firstCoreCenter H) (hz1 : z ≠ 1) :
    ∃ hzP : z ∈ secondParabolic T M Mc H,
      (r.right ⟨z,hzP⟩).val = long P hp2 2 1 := by
  have hzQ : z ∈ H.pCoreIn 2 := (map_subtype_le _) hz
  have hzH := pCoreIn_le 2 H hzQ
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hTH)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTH] at hh
  have hzP : z ∈ secondParabolic T M Mc H :=
    (show (T : Subgroup G) ≤ secondParabolic T M Mc H from
      le_sup_right.trans le_sup_left) (hQT hzQ)
  refine ⟨hzP,?_⟩
  rw [←marked_endpoint_value r ⟨hzH,hzP⟩]
  have hm := marked_core_center_mem r ⟨z,hzH⟩ hz
  have hm1 : (r.left ⟨z,hzH⟩).val ≠ 1 := by
    intro hh
    exact hz1 (congrArg Subtype.val (r.left.injective
      ((Subtype.ext hh).trans (map_one r.left).symm)))
  obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1 : highestRoot P)).mp
    (show Nat.card (highestRoot P) = 2 from card_highestRoot P hp2)
  exact congrArg Subtype.val ((hw ⟨_,hm⟩ (fun he => hm1 (congrArg Subtype.val he))).trans
    (hw ⟨_,highest_long_mem⟩ (fun he => highest_long_ne_one (congrArg Subtype.val he))).symm)

omit [Finite G] in
/-- Each nonidentity plane element is conjugate to the original central
involution by an element of the actual local short centralizer. -/
theorem marked_short_plane_orbit (r : MarkedTriality T M Mc H)
    (hTH : (T : Subgroup G) ≤ H) (a : ExtensionField P) (ha : a ≠ 0)
    {z : G} (hz : z ∈ firstCoreCenter H) (hz1 : z ≠ 1)
    (x : centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H)))
    (hx : x ∈ markedShortPlane r a ha) (hx1 : (x.val : G) ≠ 1) :
    ∃ c : centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H)),
      (c.val : G) * z * (c.val : G)⁻¹ = (x.val : G) := by
  let e := markedShortCentralizerEquiv r a ha
  have hxe : (e x).val ∈ plane P := hx
  have hxne : (e x).val ≠ 1 := by
    intro he
    have hh := e.injective ((Subtype.ext he).trans (map_one e).symm)
    exact hx1 (congrArg (fun u => (u.val : G)) hh)
  obtain ⟨g,hg,he⟩ := plane_orbit P hp2 a (e x).val hxe hxne
  let c := e.symm ⟨g,hg⟩
  have hc : (r.right c.val).val = g := by
    rw [←markedShortCentralizerEquiv_val r a ha]
    change (e (e.symm ⟨g,hg⟩)).val = g
    rw [e.apply_symm_apply]
  obtain ⟨hzP,hze⟩ := marked_center_image r hTH hz hz1
  refine ⟨c,?_⟩
  have hh : r.right (c.val * ⟨z,hzP⟩ * c.val⁻¹) = r.right x.val := by
    apply Subtype.ext
    simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv]
    rw [hc,hze]
    exact he.trans (markedShortCentralizerEquiv_val r a ha x)
  exact congrArg Subtype.val (r.right.injective hh)

omit [Finite G] in
/-- The original core-center involution is an actual element of the pulled
back short-centralizer plane. -/
theorem marked_short_plane_contains_center (r : MarkedTriality T M Mc H)
    (hTH : (T : Subgroup G) ≤ H) (a : ExtensionField P) (ha : a ≠ 0)
    {z : G} (hz : z ∈ firstCoreCenter H) (hz1 : z ≠ 1) :
    ∃ zC : centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H)),
      (zC.val : G) = z ∧ zC ∈ markedShortPlane r a ha := by
  let e := markedShortCentralizerEquiv r a ha
  have hp := long_two_mem_plane P hp2 1
  let zC := e.symm ⟨long P hp2 2 1,plane_le_centralizer P hp2 a hp⟩
  have he : (r.right zC.val).val = long P hp2 2 1 := by
    rw [←markedShortCentralizerEquiv_val r a ha]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  obtain ⟨hzP,hze⟩ := marked_center_image r hTH hz hz1
  refine ⟨zC,?_,?_⟩
  · exact congrArg Subtype.val (r.right.injective (Subtype.ext (he.trans hze.symm)))
  · change (e zC).val ∈ plane P
    rw [show e zC = ⟨long P hp2 2 1,plane_le_centralizer P hp2 a hp⟩ from e.apply_symm_apply _]
    exact hp

omit [Finite G] in
/-- The pulled-back plane is exactly the normal closure of the original
central involution in the local short centralizer. -/
theorem marked_short_plane_normalClosure (r : MarkedTriality T M Mc H)
    (hTH : (T : Subgroup G) ≤ H) (a : ExtensionField P) (ha : a ≠ 0)
    (z : centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H)))
    (hz : (z.val : G) ∈ firstCoreCenter H) (hz1 : (z.val : G) ≠ 1) :
    normalClosure ({z} : Set (centralizer ({markedShortRoot r a} :
      Set (secondParabolic T M Mc H)))) = markedShortPlane r a ha := by
  let C := centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H))
  let V := markedShortPlane r a ha
  let : V.Normal := (marked_short_plane_structure r a ha).1
  have hzV : z ∈ V := by
    obtain ⟨zC,hzC,hzCV⟩ := marked_short_plane_contains_center r hTH a ha hz hz1
    have he : zC = z := Subtype.ext (Subtype.ext hzC)
    exact he ▸ hzCV
  apply le_antisymm (normalClosure_le_normal (by
    simpa only [Set.singleton_subset_iff,SetLike.mem_coe] using hzV))
  intro x hx
  by_cases hx1 : (x.val : G) = 1
  · have he : x = 1 := Subtype.ext (Subtype.ext hx1)
    exact he ▸ one_mem _
  · obtain ⟨c,hc⟩ := marked_short_plane_orbit r hTH a ha hz hz1 x hx hx1
    have he : c*z*c⁻¹ = x := Subtype.ext (Subtype.ext hc)
    exact he ▸ (inferInstance : (normalClosure ({z} : Set C)).Normal).conj_mem
      z (subset_normalClosure (Set.mem_singleton z)) c

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
