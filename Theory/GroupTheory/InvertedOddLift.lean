module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Retaining an odd image in a dihedral lift

Taking the full odd part of an element preserves the cyclic subgroup generated
by its image whenever that image has odd order. In particular, a nonidentity
involution image in a symmetric-three quotient has an inverted odd-order lift
whose image still has order three. No hypothesis on the kernel is needed.

Factor the order as a power of two times an odd number, then raise the element
to that power of two. This power operation is invertible on the odd image.
For the lifting application the element is a product of two involutions,
so its powers are inverted by the first involution.

Source: Janko–Thompson, Math. Z. 113 (1970), Lemma 3.1, printed p.388,
the construction of the odd subgroup of `⟨x, xʸ⟩`.
-/

namespace MonoidHom

/-- The odd part retains the whole cyclic image, without any kernel condition. -/
public theorem exists_odd_power_preserving_zpowers_image
    {G K : Type*} [Group G] [Finite G] [Group K]
    (f : G →* K) (x : G) (hodd : Odd (orderOf (f x))) :
    ∃ r : G, r ∈ Subgroup.zpowers x ∧ Odd (orderOf r) ∧
      Subgroup.zpowers (f r) = Subgroup.zpowers (f x) := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  let r := x ^ (2 ^ k)
  have hrpow : r ^ m = 1 := by
    rw [← pow_mul, ← hn]
    exact pow_orderOf_eq_one x
  have hrcoprime : Nat.Coprime (2 ^ k) (orderOf (f x)) :=
    hodd.coprime_two_left.pow_left k
  refine ⟨r, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _,
    hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hrpow), ?_⟩
  apply le_antisymm
  · apply Subgroup.zpowers_le.mpr
    change f (x ^ (2 ^ k)) ∈ Subgroup.zpowers (f x)
    rw [map_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · apply Subgroup.zpowers_le.mpr
    obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime (x := f x) hrcoprime
    rw [← hn]
    have hf : (f x) ^ (2 ^ k) = f r := (map_pow f x _).symm
    rw [hf]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

end MonoidHom

namespace Subgroup

/-- Odd extraction from a product of involutions retains its odd cyclic image. -/
public theorem exists_inverted_odd_of_involution_product
    {G K : Type*} [Group G] [Finite G] [Group K]
    (f : G →* K) (w v : G) (hw : w ^ 2 = 1) (hv : v ^ 2 = 1)
    (hodd : Odd (orderOf (f (w * v)))) :
    ∃ r : G, r ∈ zpowers (w * v) ∧ Odd (orderOf r) ∧
      zpowers (f r) = zpowers (f (w * v)) ∧ w * r * w⁻¹ = r⁻¹ := by
  obtain ⟨r, hr, hro, himage⟩ := f.exists_odd_power_preserving_zpowers_image (w * v) hodd
  refine ⟨r, hr, hro, himage, ?_⟩
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hw)
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hv)
  have hinv : w * (w * v) * w⁻¹ = (w * v)⁻¹ := by
    calc
      w * (w * v) * w⁻¹ = w ^ 2 * v * w⁻¹ := by simp only [pow_two, mul_assoc]
      _ = (w * v)⁻¹ := by rw [hw, one_mul, mul_inv_rev, hvi]
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hr
  change MulAut.conj w ((w * v) ^ n) = ((w * v) ^ n)⁻¹
  rw [map_zpow]
  change (w * (w * v) * w⁻¹) ^ n = ((w * v) ^ n)⁻¹
  rw [hinv, inv_zpow]

private theorem perm_three_involution_product :
    ∀ t : Equiv.Perm (Fin 3), t ^ 2 = 1 → t ≠ 1 →
      ∃ u : Equiv.Perm (Fin 3),
        (t * (u * t * u⁻¹)) ^ 3 = 1 ∧ t * (u * t * u⁻¹) ≠ 1 := by
  decide +kernel

/-- An involution above S₃ inverts an odd-order element with order-three image.
The odd-order element need not itself have order three. -/
public theorem exists_inverted_odd_of_surjective_perm_three
    {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (w : G) (hw : w ^ 2 = 1) (hfw : f w ≠ 1) :
    ∃ r : G, Odd (orderOf r) ∧ orderOf (f r) = 3 ∧ w * r * w⁻¹ = r⁻¹ := by
  obtain ⟨u, hu3, hune⟩ := perm_three_involution_product (f w)
    (by rw [← map_pow, hw, map_one]) hfw
  obtain ⟨g, rfl⟩ := hf u
  let v := g * w * g⁻¹
  have hv : v ^ 2 = 1 := by
    change (MulAut.conj g w) ^ 2 = 1
    rw [← map_pow, hw, map_one]
  have hfx : orderOf (f (w * v)) = 3 := by
    apply orderOf_eq_prime
    · simpa only [v, map_mul, map_inv] using hu3
    · simpa only [v, map_mul, map_inv] using hune
  obtain ⟨r, _, hro, himage, hinv⟩ := exists_inverted_odd_of_involution_product
    f w v hw hv (by rw [hfx]; decide)
  have heq : orderOf (f r) = orderOf (f (w * v)) := by
    apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_mem_zpowers
      rw [← himage]
      exact mem_zpowers _
    · apply orderOf_dvd_of_mem_zpowers
      rw [himage]
      exact mem_zpowers _
  exact ⟨r, hro, heq.trans hfx, hinv⟩

end Subgroup
