module

public import Theory.GroupTheory.ElementaryEightPlaneOrder24
public import Theory.GroupTheory.ElementaryEightFixedPointOrder24
public import Theory.GroupTheory.ElementaryEightNormalizerRecognition

/-!
# Incompatible plane and point stabilizers on an elementary eight

Two order-24 subgroups of the actual conjugation image, one preserving a
plane and the other fixing a nonidentity point, force a nonsolvable
normalizer. They are distinct: the plane stabilizer fixes no nonidentity
point. Both are symmetric groups of degree four, so the elementary-eight
normalizer recognition applies.

The image packages retain the actual normalizer action. This separates the
linear argument from the construction of the elementary subgroup and its
local actors in the order-64 branch of Stellmacher (8.6)(a),
`refs/latex/stellmacher-n-group.tex`.
-/

/-- An order-24 subgroup of the actual automizer preserving a plane. -/
public structure ElementaryEightPlaneImage
    {G : Type*} [Group G] (U : Subgroup G) where
  W : Subgroup U
  plane_card : Nat.card W = 4
  J : Subgroup (MulAut U)
  image_card : Nat.card J = 24
  le_range : J ≤ U.normalizerMonoidHom.range
  stable : ∀ j : J, ∀ u : U, (j : MulAut U) u ∈ W ↔ u ∈ W

/-- An order-24 subgroup of the actual automizer fixing a nonidentity point. -/
public structure ElementaryEightPointImage
    {G : Type*} [Group G] (U : Subgroup G) where
  z : U
  ne_one : z ≠ 1
  J : Subgroup (MulAut U)
  image_card : Nat.card J = 24
  le_range : J ≤ U.normalizerMonoidHom.range
  fixed : ∀ j : J, (j : MulAut U) z = z

/-- A normalizing subgroup of order 192 with centralizer exactly the eight
and an invariant plane realizes the required order-24 plane image. -/
public theorem elementaryEight_plane_image_of_normalizing_subgroup
    {G : Type*} [Group G] [Finite G] (U P : Subgroup G)
    (hU : Nat.card U = 8) (hP : Nat.card P = 192)
    (hPN : P ≤ Subgroup.normalizer (U : Set G))
    (hcentral : P ⊓ Subgroup.centralizer (U : Set G) = U)
    (W : Subgroup U) (hW : Nat.card W = 4)
    (hstable : ∀ p : P, ∀ u : U,
      U.normalizerMonoidHom (Subgroup.inclusion hPN p) u ∈ W ↔ u ∈ W) :
    Nonempty (ElementaryEightPlaneImage U) := by
  let f := U.normalizerMonoidHom.comp (Subgroup.inclusion hPN)
  have hUP : U ≤ P := hcentral ▸ inf_le_left
  have hker : f.ker = U.subgroupOf P := by
    ext p
    change Subgroup.inclusion hPN p ∈ U.normalizerMonoidHom.ker ↔ (p : G) ∈ U
    rw [Subgroup.normalizerMonoidHom_ker]
    change (p : G) ∈ Subgroup.centralizer (U : Set G) ↔ (p : G) ∈ U
    conv_rhs => rw [← hcentral]
    simp only [Subgroup.mem_inf, p.property, true_and]
  have hrange : Nat.card f.range = 24 := by
    have h := f.ker.index_mul_card
    rw [Subgroup.index_ker, hker, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hUP).toEquiv, hU, hP] at h
    omega
  refine ⟨⟨W, hW, f.range, hrange, ?_, ?_⟩⟩
  · rintro _ ⟨p, rfl⟩
    exact ⟨Subgroup.inclusion hPN p, rfl⟩
  · rintro ⟨_, p, rfl⟩ u
    exact hstable p u

/-- A self-centralizing elementary eight in an order-64 normalizing subgroup,
together with a cubic automorphism fixing the same nonidentity point as that
subgroup, supplies the full point stabilizer in the actual automizer. -/
public theorem elementaryEight_point_image_of_cubic
    {G : Type*} [Group G] [Finite G] (U S : Subgroup G)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8) (hS : Nat.card S = 64)
    (hSN : S ≤ Subgroup.normalizer (U : Set G))
    (hcentral : S ⊓ Subgroup.centralizer (U : Set G) = U)
    (z : U) (hz : z ≠ 1)
    (hfixS : ∀ s : S, U.normalizerMonoidHom (Subgroup.inclusion hSN s) z = z)
    (g : Subgroup.normalizer (U : Set G))
    (hg : orderOf (U.normalizerMonoidHom g) = 3)
    (hfixg : U.normalizerMonoidHom g z = z) :
    Nonempty (ElementaryEightPointImage U) := by
  let f := U.normalizerMonoidHom.comp (Subgroup.inclusion hSN)
  have hUS : U ≤ S := hcentral ▸ inf_le_left
  have hker : f.ker = U.subgroupOf S := by
    ext s
    change Subgroup.inclusion hSN s ∈ U.normalizerMonoidHom.ker ↔ (s : G) ∈ U
    rw [Subgroup.normalizerMonoidHom_ker]
    change (s : G) ∈ Subgroup.centralizer (U : Set G) ↔ (s : G) ∈ U
    conv_rhs => rw [← hcentral]
    simp only [Subgroup.mem_inf, s.property, true_and]
  have hrange : Nat.card f.range = 8 := by
    have h := f.ker.index_mul_card
    rw [Subgroup.index_ker, hker, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hUS).toEquiv, hU, hS] at h
    omega
  let e := U.normalizerMonoidHom g
  let J := f.range ⊔ Subgroup.zpowers e
  have hJR : J ≤ U.normalizerMonoidHom.range := by
    apply sup_le
    · rintro _ ⟨s, rfl⟩
      exact ⟨Subgroup.inclusion hSN s, rfl⟩
    · exact Subgroup.zpowers_le.mpr ⟨g, rfl⟩
  have hfix : ∀ j : J, (j : MulAut U) z = z := by
    have hJ : J ≤ MulAction.stabilizer (MulAut U) z := by
      apply sup_le
      · rintro _ ⟨s, rfl⟩
        exact hfixS s
      · exact Subgroup.zpowers_le.mpr hfixg
    intro j
    exact hJ j.property
  have hd8 : 8 ∣ Nat.card J := hrange ▸ Subgroup.card_dvd_of_le
    (show f.range ≤ J from le_sup_left)
  have hd3 : 3 ∣ Nat.card J := by
    have he : e ∈ J := Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
    have h := orderOf_dvd_natCard (⟨e, he⟩ : J)
    rw [← Subgroup.orderOf_coe] at h
    simpa only [e, hg] using h
  have h24 : 24 ∣ Nat.card J :=
    (show Nat.Coprime 8 3 by decide).mul_dvd_of_dvd_of_dvd hd8 hd3
  exact ⟨⟨z, hz, J, Nat.dvd_antisymm
    (elementaryEight_fixed_point_image_card_dvd_twentyfour hU z hz J hfix) h24,
    hJR, hfix⟩⟩

/-- Plane and point stabilizers in the actual image force a nonsolvable
normalizer of the elementary subgroup. -/
public theorem elementaryEight_normalizer_not_isSolvable_of_plane_point
    {G : Type*} [Group G] [Finite G] (U : Subgroup G)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (plane : ElementaryEightPlaneImage U) (point : ElementaryEightPointImage U) :
    ¬ Group.IsSolvable (Subgroup.normalizer (U : Set G)) := by
  have hne : plane.J ≠ point.J := by
    intro heq
    apply point.ne_one
    apply elementaryEight_plane_order24_fixed_eq_one hU plane.W plane.plane_card
      plane.J plane.image_card plane.stable point.z
    intro j
    exact point.fixed ⟨j, heq ▸ j.property⟩
  let X := plane.J.subgroupOf U.normalizerMonoidHom.range
  let Y := point.J.subgroupOf U.normalizerMonoidHom.range
  have hXY : X ≠ Y := by
    intro heq
    apply hne
    have h := congrArg
      (fun J : Subgroup U.normalizerMonoidHom.range =>
        J.map U.normalizerMonoidHom.range.subtype) heq
    simpa only [X, Y, Subgroup.map_subgroupOf_eq_of_le plane.le_range,
      Subgroup.map_subgroupOf_eq_of_le point.le_range] using h
  obtain ⟨eX⟩ := elementaryEight_plane_order24_equiv_S4 hU plane.W plane.plane_card
    plane.J plane.image_card plane.stable
  obtain ⟨eY⟩ := elementaryEight_fixed_point_order24_equiv_S4 hU point.z point.ne_one
    point.J point.image_card point.fixed
  exact elementaryEight_normalizer_not_isSolvable_of_two_symmetric_four_images
    U hU X Y hXY
    ⟨(Subgroup.subgroupOfEquivOfLe plane.le_range).trans eX⟩
    ⟨(Subgroup.subgroupOfEquivOfLe point.le_range).trans eY⟩
