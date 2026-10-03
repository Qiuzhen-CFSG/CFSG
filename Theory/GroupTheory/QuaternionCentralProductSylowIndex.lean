module

public import Theory.GroupTheory.QuaternionCentralProductAutomorphisms
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow index above a self-centralizing quaternion central product

Conjugation on a normal self-centralizing subgroup with center of order two
has kernel of order two. If that subgroup is a central product of two
quaternion eights, its automorphism order divides 1152, so the ambient order
divides 2304. For a core of order 32 the index therefore divides 72, and its
two-part is at most eight.

This is the order bound preceding the outer-action case split in
Janko–Thompson (1970), §4, printed p.390. It does not identify the quotient
of order eight or assert the existence of the quaternion factors.
-/

namespace Subgroup

variable {K : Type*} [Group K] [Finite K]

/-- The ambient order bound supplied by two quaternion factors of a normal
self-centralizing subgroup. -/
public theorem card_dvd_of_selfCentralizing_quaternion_factors
    (H : Subgroup K) [H.Normal]
    (hcentral : centralizer (H : Set K) ≤ H)
    (hZ : Nat.card (center H) = 2)
    (B C : Subgroup H)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup H) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hjoin : B ⊔ C = ⊤) : Nat.card K ∣ 2304 := by
  let f : K →* MulAut H := MulAut.conjNormal
  have hk : f.ker = centralizer (H : Set K) := by
    ext g
    rw [MonoidHom.mem_ker, mem_centralizer_iff]
    constructor
    · intro h r hr
      have hh := congrArg (fun a : MulAut H => (a ⟨r, hr⟩ : K)) h
      change g * r * g⁻¹ = r at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro h
      ext r
      change g * (r : K) * g⁻¹ = (r : K)
      rw [← h r r.property, mul_inv_cancel_right]
  have hc : centralizer (H : Set K) = (center H).map H.subtype := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x, hcentral hx⟩, mem_center_iff.mpr ?_, rfl⟩
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hx y y.property)
    · rintro ⟨x, hx, rfl⟩
      intro y hy
      exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)
  have hker : Nat.card f.ker = 2 := by
    rw [hk, hc, card_map_of_injective H.subtype_injective, hZ]
  have hrange : Nat.card f.range ∣ 1152 :=
    f.range.card_subgroup_dvd_card.trans
      (card_mulAut_dvd_of_quaternion_central_product B C hB hC hinter hcomm hjoin)
  have hcount := f.ker.card_mul_index
  rw [index_ker, hker] at hcount
  have hd := Nat.mul_dvd_mul_left 2 hrange
  rw [hcount] at hd
  exact hd

/-- Above a normal self-centralizing quaternion central product of order 32,
a Sylow two-subgroup has relative index at most eight. -/
public theorem sylow_relIndex_le_eight_of_quaternion_factors
    (H : Subgroup K) [H.Normal]
    (hcentral : centralizer (H : Set K) ≤ H)
    (hZ : Nat.card (center H) = 2) (hH : Nat.card H = 32)
    (B C : Subgroup H)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup H) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hjoin : B ⊔ C = ⊤) (T : Sylow 2 K) : H.relIndex T ≤ 8 := by
  have hcard := card_dvd_of_selfCentralizing_quaternion_factors
    H hcentral hZ B C hB hC hinter hcomm hjoin
  have hindex : H.index ∣ 72 := by
    have hcount := H.card_mul_index
    rw [hH] at hcount
    rw [← hcount] at hcard
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 32) hcard
  have hrel : H.relIndex T ∣ 72 :=
    (H.relIndex_dvd_index_of_normal T).trans hindex
  obtain ⟨n, hn⟩ := (T.isPGroup'.to_quotient (H.subgroupOf T)).exists_card_eq
  change H.relIndex T = 2 ^ n at hn
  have hnle : n ≤ 3 := by
    by_contra h
    have hd : 16 ∣ 72 := (show 2 ^ 4 ∣ 2 ^ n from
      pow_dvd_pow 2 (by omega)).trans (hn ▸ hrel)
    norm_num at hd
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hnle

end Subgroup
