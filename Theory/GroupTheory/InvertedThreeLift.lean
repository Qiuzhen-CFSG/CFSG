module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.PGroup

/-!
# Inverted subgroups of order three above a symmetric quotient

Let a finite group map onto the symmetric group on three letters. Every
involution with nonidentity image inverts a subgroup of order three. If the
kernel is a two-group, the subgroup maps injectively and its image also has
order three.

Choose a conjugate involution whose image is a different transposition. The
product has image of order three and is inverted by the original involution.
Taking the appropriate power produces an element of order three, still
inverted. The second result uses coprime orders to exclude the kernel.

This elementary dihedral argument supplies the inverted three-subgroup used
in Parrott, “A Characterization of the Tits' Simple Group” (1972), p. 676.
The quotient and involution hypotheses are explicit, and no solvability or
splitting theorem is needed for the first result.
-/

namespace Subgroup

private theorem perm_three_involution_product :
    ∀ t : Equiv.Perm (Fin 3), t ^ 2 = 1 → t ≠ 1 →
      ∃ u : Equiv.Perm (Fin 3),
        (t * (u * t * u⁻¹)) ^ 3 = 1 ∧ t * (u * t * u⁻¹) ≠ 1 := by
  decide +kernel

/-- A nontrivial involution image in S₃ supplies an inverted subgroup of order three. -/
public theorem exists_inverted_three_of_surjective_perm_three
    {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (w : G) (hw : w ^ 2 = 1) (hfw : f w ≠ 1) :
    ∃ Q : Subgroup G, Nat.card Q = 3 ∧
      w ∈ Subgroup.normalizer (Q : Set G) ∧
      ∀ q ∈ Q, w * q * w⁻¹ = q⁻¹ := by
  obtain ⟨u, hu3, hune⟩ := perm_three_involution_product (f w)
    (by rw [← map_pow, hw, map_one]) hfw
  obtain ⟨g, rfl⟩ := hf u
  let x := w * (g * w * g⁻¹)
  have hfx : orderOf (f x) = 3 := by
    apply orderOf_eq_prime
    · simpa only [x, map_mul, map_inv] using hu3
    · simpa only [x, map_mul, map_inv] using hune
  have hthree : 3 ∣ orderOf x := hfx ▸ orderOf_map_dvd f x
  let y := x ^ (orderOf x / 3)
  have hy : orderOf y = 3 :=
    orderOf_pow_orderOf_div (orderOf_pos x).ne' hthree
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hw)
  have hxinv : w * x * w⁻¹ = x⁻¹ := by
    calc
      w * x * w⁻¹ = w ^ 2 * (g * w * g⁻¹) * w⁻¹ := by simp only [x, pow_two, mul_assoc]
      _ = (g * w * g⁻¹) * w⁻¹ := by rw [hw, one_mul]
      _ = x⁻¹ := by simp only [x, mul_inv_rev, inv_inv, hwinv, mul_assoc]
  have hyinv : w * y * w⁻¹ = y⁻¹ := by
    change MulAut.conj w (x ^ (orderOf x / 3)) = y⁻¹
    rw [map_pow]
    change (w * x * w⁻¹) ^ (orderOf x / 3) = y⁻¹
    rw [hxinv, inv_pow]
  let Q := Subgroup.zpowers y
  have hinv : ∀ q ∈ Q, w * q * w⁻¹ = q⁻¹ := by
    intro q hq
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    change MulAut.conj w (y ^ n) = (y ^ n)⁻¹
    rw [map_zpow]
    change (w * y * w⁻¹) ^ n = (y ^ n)⁻¹
    rw [hyinv, inv_zpow]
  refine ⟨Q, ?_, ?_, hinv⟩
  · exact (Nat.card_zpowers y).trans hy
  · apply Subgroup.mem_normalizer_iff.mpr
    intro q
    constructor
    · intro hq
      rw [hinv q hq]
      exact Q.inv_mem hq
    · intro hq
      have hconj : w * (w * q * w⁻¹) * w⁻¹ ∈ Q := by
        rw [hinv _ hq]
        exact Q.inv_mem hq
      have hww : w * (w * q * w⁻¹) * w⁻¹ = q := by
        calc
          w * (w * q * w⁻¹) * w⁻¹ = w ^ 2 * q * (w ^ 2)⁻¹ := by
            simp only [pow_two, mul_inv_rev, mul_assoc]
          _ = q := by rw [hw]; simp
      exact hww ▸ hconj
/-- For a two-group kernel, the inverted subgroup lifts its order-three image faithfully. -/
public theorem exists_inverted_three_lift_of_two_kernel
    {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker)
    (w : G) (hw : w ^ 2 = 1) (hfw : f w ≠ 1) :
    ∃ Q : Subgroup G, Nat.card Q = 3 ∧
      Function.Injective (f.domRestrict Q) ∧ Nat.card (Q.map f) = 3 ∧
      w ∈ Subgroup.normalizer (Q : Set G) ∧
      ∀ q ∈ Q, w * q * w⁻¹ = q⁻¹ := by
  obtain ⟨Q, hQ, hwQ, hinv⟩ :=
    exists_inverted_three_of_surjective_perm_three f hf w hw hfw
  obtain ⟨n, hn⟩ := hker.exists_card_eq
  have hdis : Disjoint Q f.ker := Subgroup.disjoint_of_coprime_natCard (by
    rw [hQ, hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n)
  have hinj : Function.Injective (f.domRestrict Q) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro q hq
    exact Subtype.ext (Subgroup.disjoint_def.mp hdis q.property hq)
  refine ⟨Q, hQ, hinj, ?_, hwQ, hinv⟩
  rw [← MonoidHom.domRestrict_range]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hQ

end Subgroup
