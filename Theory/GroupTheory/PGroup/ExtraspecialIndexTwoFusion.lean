module

public import Theory.GroupTheory.PGroup.OrderThirtyTwoFourFusion
public import Theory.GroupTheory.PGroup.RankTwoExtraspecialThirtyTwo

/-!
# Fusion in an index-two extraspecial subgroup of order thirty-two

A centralizer in an extraspecial group has index at most two: the central
commutator homomorphism has image of order at most two. At order thirty-two,
a centralizer therefore has order at least sixteen.

Transport an involution centralizer into the Sylow centralizer of a central
involution. Its intersection with the index-two extraspecial subgroup has
order at least eight. Elementary rank at most two forces a nontrivial square
in that intersection. In both copies the square is the unique central
involution, so injectivity identifies the involutions being fused.

This proves the inside-core nonfusion needed in Janko--Thompson,
Math. Z. 113 (1970), Section 4, printed p.389, directly under the stronger
ambient elementary rank bound. No outer automorphism calculation is needed.
-/

open Subgroup
open scoped commutatorElement

/-- Every element centralizer in an extraspecial group of order thirty-two
has order at least sixteen. -/
public theorem IsExtraspecial.centralizer_card_ge_sixteen_of_card_thirty_two
    {H : Type*} [Group H] [Finite H] [IsExtraspecial 2 H]
    (hH : Nat.card H = 32) (t : H) :
    16 ≤ Nat.card (centralizer ({t} : Set H)) := by
  have hc (x : H) : ⁅t,x⁆ ∈ center H :=
    (IsExtraspecial.quotient_elementary_abelian 2 H).commutator_le_center_of_central_quotient
      (commutator_mem_commutator (mem_top t) (mem_top x))
  let d : H →* center H := {
    toFun x := ⟨⁅t,x⁆, hc x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' x y := by
      apply Subtype.ext
      change ⁅t,x*y⁆ = ⁅t,x⁆ * ⁅t,y⁆
      rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅t,x⁆ x ⁅t,y⁆,
        mem_center_iff.mp (hc y) x]
      simp only [← mul_assoc, mul_inv_cancel_right] }
  have hk : d.ker = centralizer ({t} : Set H) := by
    ext x
    change (⟨⁅t,x⁆, hc x⟩ : center H) = 1 ↔ _
    rw [Subtype.ext_iff, OneMemClass.coe_one,
      commutatorElement_eq_one_iff_mul_comm, mem_centralizer_singleton_iff]
    exact eq_comm
  have hrange : Nat.card d.range ≤ 2 := by
    simpa only [IsExtraspecial.center_order_p 2 H] using
      (Nat.card_le_card_of_injective d.range.subtype d.range.subtype_injective)
  have hd := d.ker.card_mul_index
  rw [index_ker, hk, hH] at hd
  nlinarith [Nat.mul_le_mul_left (Nat.card (centralizer ({t} : Set H))) hrange]

/-- A Sylow-central involution cannot fuse to a different involution inside
an index-two extraspecial subgroup of order thirty-two under the rank bound. -/
public theorem Sylow.eq_of_isConj_in_extraspecial_index_two_of_card_thirty_two
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup S, IsElementaryAbelian 2 A → Nat.card A < 8)
    (H : Subgroup S) [IsExtraspecial 2 H]
    (hH : Nat.card H = 32) (hi : H.index = 2)
    (z t : H) (hz : orderOf z = 2) (hzc : (z : S) ∈ center S)
    (hconj : IsConj ((z : S) : G) ((t : S) : G)) : t = z := by
  let : H.Normal := normal_of_index_eq_two hi
  let C₀ := centralizer ({t} : Set H)
  let C := C₀.map H.subtype
  have htC : (t : S) ∈ C :=
    mem_map_of_mem H.subtype (mem_centralizer_singleton_iff.mpr (Commute.refl t))
  let tC : C := ⟨t, htC⟩
  have htcentral : tC ∈ center C := by
    apply mem_center_iff.mpr
    intro x
    obtain ⟨u, hu, he⟩ := x.property
    apply Subtype.ext
    change (x : S) * (t : S) = (t : S) * (x : S)
    rw [← he]
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hu)
  obtain ⟨f, hf, hft⟩ := S.exists_injective_hom_of_central_isConj
    C tC htcentral z hzc hconj.symm
  let K := H.comap f
  have hC : 16 ≤ Nat.card C := by
    rw [card_map_of_injective H.subtype_injective]
    exact IsExtraspecial.centralizer_card_ge_sixteen_of_card_thirty_two hH t
  have hKindex : K.index ≤ 2 := by
    have hd : K.index ∣ 2 := by
      rw [show K.index = H.relIndex f.range from H.index_comap f]
      simpa only [hi] using H.relIndex_dvd_index_of_normal f.range
    exact Nat.le_of_dvd (by decide) hd
  have hK : 8 ≤ Nat.card K := by
    have hh := K.card_mul_index
    nlinarith [Nat.mul_le_mul_left (Nat.card K) hKindex]
  obtain ⟨x, hx⟩ : ∃ x : K, x ^ 2 ≠ 1 := by
    by_contra hn
    have hp : ∀ x : K, x ^ 2 = 1 := by simpa only [not_exists, not_not] using hn
    let : IsElementaryAbelian 2 K := {
      toIsMulCommutative := ⟨⟨fun a b =>
        (Commute.of_orderOf_dvd_two (fun c => orderOf_dvd_of_pow_eq_one (hp c)) a b).eq⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hp }
    have hh := (elementary_card_lt_eight_of_subgroup hrank C) K inferInstance
    omega
  have hzH : z ∈ center H := mem_center_iff.mpr (fun y =>
    Subtype.ext (mem_center_iff.mp hzc y))
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  have hsquare (y : H) (hy : y ^ 2 ≠ 1) : y ^ 2 = z := by
    obtain ⟨w, hw, hall⟩ := (Nat.card_eq_two_iff' (1 : center H)).mp
      (IsExtraspecial.center_order_p 2 H)
    exact congrArg Subtype.val
      ((hall ⟨y ^ 2, IsExtraspecial.square_mem_center y⟩
        (fun h => hy (congrArg Subtype.val h))).trans
      (hall ⟨z, hzH⟩ (fun h => hz1 (congrArg Subtype.val h))).symm)
  let y : H := ⟨((x : C) : S), map_subtype_le C₀ (x : C).property⟩
  have hy : y ^ 2 ≠ 1 := by
    intro h
    apply hx
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : H => (u : S)) h
  have hyz : (((x : C) : S)) ^ 2 = z := congrArg Subtype.val (hsquare y hy)
  let v : H := ⟨f (x : C), x.property⟩
  have hv : v ^ 2 ≠ 1 := by
    intro h
    have hvone := congrArg (fun u : H => (u : S)) h
    change f (x : C) ^ 2 = 1 at hvone
    have he : f ((x : C) ^ 2) = f 1 := by
      simpa only [map_pow, map_one] using hvone
    exact hx (Subtype.ext (hf he))
  have hvz : f (x : C) ^ 2 = z := congrArg Subtype.val (hsquare v hv)
  have hxeq : (x : C) ^ 2 = tC := hf (by simpa only [map_pow, hft] using hvz)
  apply Subtype.ext
  exact (congrArg Subtype.val hxeq).symm.trans hyz
