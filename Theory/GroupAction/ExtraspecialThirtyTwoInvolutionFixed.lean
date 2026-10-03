module

public import Theory.GroupTheory.PGroup.RankTwoExtraspecialThirtyTwo
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupAction.InvolutionDisplacementCard

/-!
# Involution fixed points in an extraspecial group of order thirty-two

An automorphism of square one fixes at least four elements of an extraspecial
group of order thirty-two. On its elementary central quotient of order sixteen,
displacement is contained in the fixed subgroup, which consequently has order
at least four. Its full preimage has twice that order. Displacement of the
preimage into the center is a homomorphism with image of order at most two,
so at least four elements of the original group are fixed.

This is the elementary centralizer bound used in Janko--Thompson,
Math. Z. 113 (1970), Section 4, printed p.389, in the index-two case.
The argument includes the identity automorphism and both extraspecial types;
it requires no classification of the outer automorphism group.
-/

open Subgroup

/-- Every automorphism of square one on an extraspecial group of order
thirty-two has a fixed subgroup of order at least four. -/
public theorem MulAut.fixed_card_ge_four_of_extraspecial_card_thirty_two
    {H : Type*} [Group H] [Finite H] [IsExtraspecial 2 H]
    (hH : Nat.card H = 32) (a : MulAut H) (ha : a ^ 2 = 1) :
    4 ≤ Nat.card (FixedPoints.subgroup (zpowers a) H) := by
  let q := QuotientGroup.mk' (center H)
  let b := quotientAut (center H) a
  let F := FixedPoints.subgroup (zpowers b) (H ⧸ center H)
  let K := F.comap q
  let C := FixedPoints.subgroup (zpowers a) H
  let : IsElementaryAbelian 2 (H ⧸ center H) :=
    IsExtraspecial.quotient_elementary_abelian 2 H
  have hb : b ^ 2 = 1 := by
    change (quotientAut (center H) a) ^ 2 = 1
    rw [← map_pow, ha, map_one]
  have hquot : Nat.card (H ⧸ center H) = 16 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (center H)
    rw [hH, IsExtraspecial.center_order_p 2 H] at hh
    omega
  obtain ⟨hcount, hle⟩ := MulAut.involution_fixed_displacement_card_data b hb
  have hlecard := card_le_of_le hle
  have hF : 4 ≤ Nat.card F := by
    change Nat.card (H ⧸ center H) = Nat.card F * _ at hcount
    rw [hquot] at hcount
    change _ ≤ Nat.card F at hlecard
    nlinarith [Nat.mul_le_mul_left (Nat.card F) hlecard]
  have hKcard : Nat.card K = 2 * Nat.card F := by
    have h1 := K.index_mul_card
    have h2 := F.index_mul_card
    have hi : K.index = F.index := F.index_comap_of_surjective
      (QuotientGroup.mk'_surjective (center H))
    rw [hi, hH] at h1
    rw [hquot] at h2
    have hipos := F.index_ne_zero_of_finite
    nlinarith
  have hdisplace (x : K) : (x : H)⁻¹ * a x ∈ center H := by
    apply (QuotientGroup.eq_one_iff (N := center H) _).mp
    change q ((x : H)⁻¹ * a x) = 1
    rw [map_mul, map_inv]
    have hf : b (q (x : H)) = q x :=
      ((FixedPoints.mem_subgroup (M := zpowers b) (a := q (x : H))).mp x.property)
        ⟨b, mem_zpowers b⟩
    rw [quotientAut_apply_mk] at hf
    rw [hf, inv_mul_cancel]
  let d : K →* center H := {
    toFun x := ⟨(x : H)⁻¹ * a x, hdisplace x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' x y := by
      apply Subtype.ext
      change ((x : H) * (y : H))⁻¹ * a ((x : H) * (y : H)) =
        ((x : H)⁻¹ * a x) * ((y : H)⁻¹ * a y)
      rw [mul_inv_rev, map_mul]
      have hc := mem_center_iff.mp (hdisplace x) (y : H)⁻¹
      calc
        _ = (y : H)⁻¹ * ((x : H)⁻¹ * a x) * a y := by group
        _ = ((x : H)⁻¹ * a x) * (y : H)⁻¹ * a y := by rw [hc]
        _ = _ := by group }
  have hker : Nat.card d.ker ≤ Nat.card C := by
    let f : d.ker → C := fun x => ⟨((x : K) : H), by
      have hx : a (((x : K) : H)) = ((x : K) : H) := by
        have hh := congrArg Subtype.val x.property
        change (((x : K) : H))⁻¹ * a (((x : K) : H)) = 1 at hh
        exact (inv_mul_eq_one.mp hh).symm
      intro k
      exact smul_eq_self_of_mem_zpowers k.property hx⟩
    apply Nat.card_le_card_of_injective f
    intro x y h
    have he := congrArg (fun u : C => (u : H)) h
    exact Subtype.ext (Subtype.ext he)
  have hrange : Nat.card d.range ≤ 2 := by
    simpa only [IsExtraspecial.center_order_p 2 H] using
      (Nat.card_le_card_of_injective d.range.subtype d.range.subtype_injective)
  have hd := d.ker.card_mul_index
  rw [index_ker] at hd
  nlinarith [Nat.mul_le_mul_left (Nat.card d.ker) hrange]
