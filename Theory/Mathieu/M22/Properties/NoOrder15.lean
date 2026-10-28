module

public import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.Mathieu.M22.Properties.ElevenFiveFrobenius
-- Internal extension of the existing permutation certificates: their private
-- concrete witnesses are used without widening the public Mathieu API.
import all Theory.Mathieu.M22.Properties.ThreeRank
import all Theory.Mathieu.M22.Properties.ElevenFiveFrobenius

/-!
# Excluding order fifteen in the concrete Mathieu group M₂₂

The eight nonidentity elements of the certified elementary abelian Sylow
three-subgroup each fix four points. The four nonidentity powers of the
certified order-five element each fix two points. Sylow conjugacy transports
these kernel-checked counts to all elements of orders three and five.

If an element had order fifteen, its fifth and third powers would commute.
The order-five power would preserve the four fixed points of the order-three
power. Its induced permutation has order dividing both five and 4!, so it
fixes all four points, contradicting its fixed-point count of two.

This proves the exclusion implied by the 5A normalizer row of GLS, volume 3,
Table 5.3c (`refs/KGroup/GLS3/Chapter5(sec3-).tex`, lines 146–173), directly
in the Steiner-design model. No normalizer-table assertion is a premise.
The private witness imports intentionally extend the existing `ThreeRank`
and `ElevenFiveFrobenius` certificates without exposing their implementation.
-/

namespace Sporadic.Mathieu
namespace M22NoOrder15
noncomputable section
open Subgroup
set_option maxRecDepth 100000

private def fixed (g : Equiv.Perm (Fin 22)) : Finset (Fin 22) :=
  Finset.univ.filter (fun x => g x = x)

private theorem mem_fixed (g : Equiv.Perm (Fin 22)) (x : Fin 22) :
    x ∈ fixed g ↔ g x = x := by simp [fixed]

private theorem fixed_conj_card (g x : M22) :
    (fixed ((MulAut.conj g x).val)).card = (fixed x.val).card := by
  have he : fixed ((MulAut.conj g x).val) = (fixed x.val).image g.val := by
    ext a
    rw [mem_fixed, Finset.mem_image]
    constructor
    · intro ha
      refine ⟨g.val.symm a, ?_, g.val.apply_symm_apply a⟩
      rw [mem_fixed]
      apply g.val.injective
      change g.val (x.val (g.val.symm a)) = g.val (g.val.symm a)
      change g.val (x.val (g.val.symm a)) = a at ha
      simpa only [Equiv.apply_symm_apply] using ha
    · rintro ⟨b, hb, rfl⟩
      rw [mem_fixed] at hb
      change g.val (x.val (g.val.symm (g.val b))) = g.val b
      rw [Equiv.symm_apply_apply, hb]
  rw [he, Finset.card_image_of_injective _ g.val.injective]

private def threeRow (ij : Fin 3 × Fin 3) : m22ThreeElementary :=
  ⟨rankX ^ ij.1.val * rankY ^ ij.2.val,
    m22ThreeElementary.mul_mem
      (m22ThreeElementary.pow_mem
        ((show zpowers rankX ≤ m22ThreeElementary from le_sup_left) (mem_zpowers rankX)) _)
      (m22ThreeElementary.pow_mem
        ((show zpowers rankY ≤ m22ThreeElementary from le_sup_right) (mem_zpowers rankY)) _)⟩

private theorem threeRow_injective : Function.Injective threeRow := by
  have hk : Function.Injective (fun ij : Fin 3 × Fin 3 =>
      (rankXPerm ^ ij.1.val * rankYPerm ^ ij.2.val) (0 : Fin 22)) := by
    decide +kernel
  intro i j h
  exact hk (congrArg (fun z : m22ThreeElementary => z.val.val (0 : Fin 22)) h)

private theorem threeRow_surjective : Function.Surjective threeRow :=
  (threeRow_injective.bijective_of_nat_card_le (by
    simp only [m22ThreeElementary_card, Nat.card_prod, Nat.card_fin]
    decide)).2

private theorem threeRow_fixed (ij : Fin 3 × Fin 3) (hij : ij ≠ (0, 0)) :
    (fixed (threeRow ij).val.val).card = 4 := by
  have hc : ∀ ij : Fin 3 × Fin 3, ij ≠ (0, 0) →
      (fixed (rankXPerm ^ ij.1.val * rankYPerm ^ ij.2.val)).card = 4 := by
    decide +kernel
  exact hc ij hij

private theorem three_fixed (x : M22) (hx : orderOf x = 3) :
    (fixed x.val).card = 4 := by
  have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M22 Q m22ThreeSylow
  let e := MulAut.conj g
  have hmem : e x ∈ m22ThreeElementary := by
    rw [← m22ThreeSylow_coe, ← hg]
    change e x ∈ (Q : Subgroup M22).map e.toMonoidHom
    exact mem_map_of_mem e.toMonoidHom (hQ (mem_zpowers x))
  obtain ⟨ij, hij⟩ := threeRow_surjective ⟨e x, hmem⟩
  have hij0 : ij ≠ (0, 0) := by
    intro he
    have hx1 : e x = 1 := by
      have hh := congrArg Subtype.val hij
      simpa only [he, threeRow, Fin.val_zero, pow_zero, one_mul] using hh.symm
    have := (e.orderOf_eq x).trans hx
    rw [hx1, orderOf_one] at this
    norm_num at this
  have hc := threeRow_fixed ij hij0
  have he := congrArg Subtype.val hij
  rw [he] at hc
  exact (fixed_conj_card g x).symm.trans hc

private theorem five_fixed (x : M22) (hx : orderOf x = 5) :
    (fixed x.val).card = 2 := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let P := frobFiveSylow (zpowers x) (by rwa [Nat.card_zpowers])
  let Q := frobFiveSylow (zpowers frobY) (by rw [Nat.card_zpowers, frobY_order])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M22 P Q
  let e := MulAut.conj g
  have hmem : e x ∈ zpowers frobY := by
    change e x ∈ (Q : Subgroup M22)
    rw [← hg]
    change e x ∈ (P : Subgroup M22).map e.toMonoidHom
    exact mem_map_of_mem e.toMonoidHom (mem_zpowers x)
  rw [mem_zpowers_iff_mem_range_orderOf, frobY_order] at hmem
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hmem
  have hi0 : i ≠ 0 := by
    intro h
    have hx1 : e x = 1 := by simpa [h] using he.symm
    have := (e.orderOf_eq x).trans hx
    rw [hx1, orderOf_one] at this
    norm_num at this
  have hc : ∀ i : Fin 5, i ≠ 0 → (fixed (frobYPerm ^ i.val)).card = 2 := by
    decide +kernel
  have hci := hc ⟨i, Finset.mem_range.mp hi⟩ (by simpa using hi0)
  have hcast : (frobY ^ i).val = frobYPerm ^ i := rfl
  rw [← hcast, he] at hci
  exact (fixed_conj_card g x).symm.trans hci


private theorem fixed_subset_of_commute (t y : M22)
    (ht : (fixed t.val).card = 4) (hy : orderOf y = 5) (hc : Commute t y) :
    fixed t.val ⊆ fixed y.val := by
  have hinv : ∀ a, y.val a ∈ fixed t.val ↔ a ∈ fixed t.val := by
    intro a
    rw [mem_fixed, mem_fixed]
    have he : t.val (y.val a) = y.val (t.val a) :=
      congrArg (fun g : M22 => g.val a) hc.eq
    rw [he, y.val.injective.eq_iff]
  let r : Equiv.Perm (fixed t.val) := y.val.subtypePerm hinv
  have hr5 : r ^ 5 = 1 := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    change ((y.val.subtypePerm hinv ^ 5) a).val = a.val
    rw [Equiv.Perm.subtypePerm_apply_pow_of_mem]
    change (y ^ 5).val a.val = a.val
    rw [← hy, pow_orderOf_eq_one]
    rfl
  have hd24 : orderOf r ∣ 24 := by
    have hd := orderOf_dvd_natCard r
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe,
      ht, show Nat.factorial 4 = 24 by decide] using hd
  have hr1 : r = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 5 24)
      (orderOf_dvd_of_pow_eq_one hr5) hd24)
  intro a ha
  rw [mem_fixed]
  exact congrArg (fun f : Equiv.Perm (fixed t.val) => (f ⟨a, ha⟩).val) hr1

end
end M22NoOrder15

/-- The Steiner-design Mathieu group M₂₂ has no element of order fifteen. -/
public theorem m22_orderOf_ne_fifteen (x : M22) : orderOf x ≠ 15 := by
  intro hx
  have ht : orderOf (x ^ 5) = 3 := by rw [orderOf_pow, hx]; decide
  have hy : orderOf (x ^ 3) = 5 := by rw [orderOf_pow, hx]; decide
  have hs := M22NoOrder15.fixed_subset_of_commute (x ^ 5) (x ^ 3)
    (M22NoOrder15.three_fixed _ ht) hy (Commute.pow_pow_self x 5 3)
  have hn := Finset.card_le_card hs
  rw [M22NoOrder15.three_fixed _ ht, M22NoOrder15.five_fixed _ hy] at hn
  omega

end Sporadic.Mathieu
