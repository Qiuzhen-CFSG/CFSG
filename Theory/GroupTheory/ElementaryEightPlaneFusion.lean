module

public import Theory.GroupTheory.ElementaryEightPlanePoint

/-!
# Fusion and centralizers in an elementary-eight plane stabilizer

For an elementary subgroup of order eight whose actual automizer contains
an order-24 plane stabilizer, the nonidentity plane points are conjugate.
Every point outside the plane has ambient centralizer order divisible by
three. Indeed its stabilizer in the action image has order six; lifting
that stabilizer to the normalizer gives a subgroup of the ambient centralizer.

This is the elementary local-action step in Thompson VI, printed p.628:
the cubic actor centralizes the point outside the plane spanned by Z and Z*.
-/

open Subgroup

/-- A subgroup of the actual automizer fixing a point has order dividing
that point's ambient centralizer order. -/
public theorem Subgroup.card_dvd_centralizer_of_fixed_automizer
    {G : Type*} [Group G] [Finite G] (U : Subgroup G)
    (J : Subgroup (MulAut U)) (hJ : J ≤ U.normalizerMonoidHom.range)
    (x : U) (hfix : ∀ j : J, (j : MulAut U) x = x) :
    Nat.card J ∣ Nat.card (centralizer ({(x : G)} : Set G)) := by
  let C := centralizer ({(x : G)} : Set G)
  let N := normalizer (U : Set G)
  let B := C.subgroupOf N
  let f : B →* MulAut U := U.normalizerMonoidHom.comp B.subtype
  have hle : J ≤ f.range := by
    intro j hj
    obtain ⟨n, hn⟩ := hJ hj
    have hnC : (n : G) ∈ C := by
      have hh := congrArg Subtype.val (hfix ⟨j, hj⟩)
      change ((j x : U) : G) = (x : G) at hh
      rw [← hn] at hh
      change (n : G) * (x : G) * (n : G)⁻¹ = (x : G) at hh
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh)
    exact ⟨⟨n, hnC⟩, hn⟩
  let inclusion : B →* C := {
    toFun b := ⟨((b : N) : G), b.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hinj : Function.Injective inclusion := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun c : C => (c : G)) h))
  exact (card_dvd_of_le hle).trans
    ((card_dvd_of_surjective f.rangeRestrict f.rangeRestrict_surjective).trans
      (card_dvd_of_injective inclusion hinj))

/-- All nonidentity points in the plane fuse to any chosen nonidentity
plane point; the remaining points have a centralizer factor three. -/
public theorem elementaryEight_plane_involution_alternative
    {G : Type*} [Group G] [Finite G] (U : Subgroup G)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (plane : ElementaryEightPlaneImage U)
    (z : U) (hz : z ∈ plane.W) (hz1 : z ≠ 1)
    (x : U) (hx1 : x ≠ 1) :
    IsConj (z : G) (x : G) ∨
      3 ∣ Nat.card (centralizer ({(x : G)} : Set G)) := by
  by_cases hx : x ∈ plane.W
  · obtain ⟨j, hj⟩ := elementaryEight_plane_order24_plane_transitive
      hU plane.W plane.plane_card plane.J plane.image_card plane.stable z x hz hx hz1 hx1
    obtain ⟨n, hn⟩ := plane.le_range j.property
    left
    apply isConj_iff.mpr
    refine ⟨(n : G), ?_⟩
    have hh := congrArg Subtype.val hj
    rw [← hn] at hh
    exact hh
  · right
    let B := MulAction.stabilizer plane.J x
    have hB : Nat.card B = 6 := elementaryEight_plane_order24_outside_stabilizer_card
      hU plane.W plane.plane_card plane.J plane.image_card plane.stable x hx
    let J := B.map plane.J.subtype
    have hJ : J ≤ U.normalizerMonoidHom.range :=
      (map_subtype_le B).trans plane.le_range
    have hfixed : ∀ j : J, (j : MulAut U) x = x := by
      rintro ⟨j, b, hb, rfl⟩
      exact hb
    have hcard : Nat.card J = 6 := (card_map_of_injective plane.J.subtype_injective).trans hB
    have hdiv := U.card_dvd_centralizer_of_fixed_automizer J hJ x hfixed
    rw [hcard] at hdiv
    exact (by decide : 3 ∣ 6).trans hdiv
