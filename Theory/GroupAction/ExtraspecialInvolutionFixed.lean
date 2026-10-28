module

public import Theory.ElementaryAbelian.Extraspecial
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupAction.InvolutionDisplacementCard

/-!
# Fixed points of involutions on extraspecial two-groups

An involution on an extraspecial group P fixes at least the square root
of |P/Z(P)|. On the elementary central quotient, displacement lies in
the fixed subgroup. The fixed subgroup downstairs is no larger than the
one upstairs: its full inverse image has a central displacement
homomorphism with image of order at most two.

This extends the order-32 argument in `ExtraspecialThirtyTwoInvolutionFixed`.
The order-512 instance is used in Aschbacher–Smith, Lemma 14.4.9,
printed p.1010, to inspect the exchanged involution centralizer.
-/

public section
open Subgroup

/-- The square of the fixed-subgroup order bounds the central quotient order. -/
theorem MulAut.extraspecial_card_le_twice_fixed_card_sq
    {H : Type*} [Group H] [Finite H] [IsExtraspecial 2 H]
    (a : MulAut H) (ha : a ^ 2 = 1) :
    Nat.card H ≤ 2 * Nat.card (FixedPoints.subgroup (zpowers a) H) ^ 2 := by
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
  have hquot : Nat.card H = 2 * Nat.card (H ⧸ center H) := by
    simpa only [IsExtraspecial.center_order_p 2 H, mul_comm] using
      card_eq_card_quotient_mul_card_subgroup (center H)
  obtain ⟨hcount, hle⟩ := MulAut.involution_fixed_displacement_card_data b hb
  have hlecard := card_le_of_le hle
  have hF : Nat.card (H ⧸ center H) ≤ Nat.card F ^ 2 := by
    change Nat.card (H ⧸ center H) = Nat.card F * _ at hcount
    change _ ≤ Nat.card F at hlecard
    rw [hcount, pow_two]
    exact Nat.mul_le_mul_left _ hlecard
  have hKcard : Nat.card K = 2 * Nat.card F := by
    have h1 := K.index_mul_card
    have h2 := F.index_mul_card
    have hi : K.index = F.index := F.index_comap_of_surjective
      (QuotientGroup.mk'_surjective (center H))
    rw [hi, hquot, ← h2] at h1
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero F.index_ne_zero_of_finite)
      (h1.trans (by ring))
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
  have hFC : Nat.card F ≤ Nat.card C := by
    have hh := Nat.mul_le_mul hker hrange
    rw [hd, hKcard] at hh
    omega
  calc
    Nat.card H = 2 * Nat.card (H ⧸ center H) := hquot
    _ ≤ 2 * Nat.card F ^ 2 := Nat.mul_le_mul_left _ hF
    _ ≤ 2 * Nat.card C ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hFC 2)
