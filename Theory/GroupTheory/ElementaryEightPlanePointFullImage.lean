module
public import Theory.GroupTheory.ElementaryEightPlanePoint

/-!
# Full and nonsolvable elementary-eight automizers

A plane stabilizer and a point stabilizer of order 24 in the actual
normalizer image are distinct. The plane stabilizer has prime index seven
in the full automorphism group, so the image is all of Aut(E). The literal
image is nonsolvable: its kernel quotient is PSL3(2).

These statements keep the conjugation kernel, unlike nonsolvability of the
whole normalizer, and support the source 14.1.6 obstruction to the Omega
extension in Aschbacher--Smith 15.1.11, printed p.1089.
-/

public section
open Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem elementaryEight_normalizerMonoidHom_surjective_of_plane_point (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (plane : ElementaryEightPlaneImage E) (point : ElementaryEightPointImage E) :
    Function.Surjective E.normalizerMonoidHom := by
  have hne : plane.J ≠ point.J := by
    intro heq
    apply point.ne_one
    apply elementaryEight_plane_order24_fixed_eq_one hE plane.W plane.plane_card
      plane.J plane.image_card plane.stable point.z
    exact fun j => point.fixed ⟨j, heq ▸ j.property⟩
  have hc := card_mulAut_of_elementary_eight E hE
  have hi : plane.J.index = 7 := by
    have h := plane.J.card_mul_index
    rw [plane.image_card, hc] at h
    omega
  have hd : E.normalizerMonoidHom.range.index ∣ 7 := by
    rw [← hi]
    exact index_dvd_of_le plane.le_range
  rcases (show Nat.Prime 7 by decide).eq_one_or_self_of_dvd _ hd with h | h
  · exact MonoidHom.range_eq_top.mp (index_eq_one.mp h)
  · have hr : Nat.card E.normalizerMonoidHom.range = 24 := by
      have he := E.normalizerMonoidHom.range.card_mul_index
      rw [h, hc] at he
      omega
    exact (hne ((eq_of_le_of_card_ge plane.le_range (by rw [hr, plane.image_card])).trans
      (eq_of_le_of_card_ge point.le_range (by rw [hr, point.image_card])).symm)).elim

theorem elementaryEight_normalizerImage_not_isSolvable_of_plane_point (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (plane : ElementaryEightPlaneImage E) (point : ElementaryEightPointImage E) :
    ¬ Group.IsSolvable E.normalizerMonoidHom.range := by
  have hne : plane.J ≠ point.J := by
    intro heq
    apply point.ne_one
    apply elementaryEight_plane_order24_fixed_eq_one hE plane.W plane.plane_card
      plane.J plane.image_card plane.stable point.z
    exact fun j => point.fixed ⟨j, heq ▸ j.property⟩
  let X := plane.J.subgroupOf E.normalizerMonoidHom.range
  let Y := point.J.subgroupOf E.normalizerMonoidHom.range
  have hXY : X ≠ Y := by
    intro heq
    apply hne
    have h := congrArg (fun J : Subgroup E.normalizerMonoidHom.range =>
      J.map E.normalizerMonoidHom.range.subtype) heq
    simpa only [X, Y, map_subgroupOf_eq_of_le plane.le_range,
      map_subgroupOf_eq_of_le point.le_range] using h
  obtain ⟨eX⟩ := elementaryEight_plane_order24_equiv_S4 hE plane.W plane.plane_card
    plane.J plane.image_card plane.stable
  obtain ⟨eY⟩ := elementaryEight_fixed_point_order24_equiv_S4 hE point.z point.ne_one
    point.J point.image_card point.fixed
  obtain ⟨f,hf,hk⟩ := elementaryEight_normalizer_centralizer_quotient_PSL3 E hE X Y hXY
    ⟨(subgroupOfEquivOfLe plane.le_range).trans eX⟩
    ⟨(subgroupOfEquivOfLe point.le_range).trans eY⟩
  let eqr := (QuotientGroup.quotientKerEquivRange E.normalizerMonoidHom).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      ((normalizerMonoidHom_ker E).trans hk.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf))
  intro hs
  exact not_isSolvable_psl3_two
    (Group.isSolvable_of_surjective (f := eqr.toMonoidHom) eqr.surjective)

