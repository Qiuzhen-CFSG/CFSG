module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.LocalCounts.Inverting.LocalNormalizer
public import Theory.GroupTheory.ThreeInverterCosets
public import Theory.GroupTheory.CyclicThreeFifteenActions

/-!
# Ambient involutions inverting a local element of order three

The actual alternating centralizer supplies a commuting pair of involutions
`z,t`, with `t` inverting `x`. The odd cyclic factor `A` of `C_G(x)` is
preserved by both involutions. Every inverter lies uniquely in `At` or `Azt`.
The involution condition becomes inversion of its `A` coordinate. The fixed
subgroup of `z` in `A` has order three, so the cyclic-action calculation gives
six inverters when `|A| = 3` and eighteen when `|A| = 15`.

Only `x` is restricted to the distinguished centralizer. The counted
involutions range over the entire ambient group. The centralizer structure
(4.1) is the sole additional premise; no inversion count or normalizer model
is assumed.

Source: Bender, *Finite groups with large subgroups* (1974), §4, printed
pp.225–226, the inversion assertion of (4.2).
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]

/-- Bender's ambient order-three inversion count, from the structural
centralizer decomposition and the actual local model. -/
public theorem inverting_three_count_of_structure
    (h : Janko1CentralizerData G) (s : OddPrimeCentralizerStructure h)
    (x : G) (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = 3) :
    Nat.card {t : G // orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹} =
      if Nat.card (centralizer ({x} : Set G)) = 6 then 6 else 18 := by
  obtain ⟨t, A, htz, ht, htx, hcyc, hcard, hNA, hd, hprod, hxA, hfixed⟩ :=
    h.exists_three_inversion_structure_of_structure s x hxC hx
  let : IsCyclic A := hcyc
  have hzC : h.z ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hxC).symm
  have hzN : h.z ∈ normalizer (zpowers x : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (h.z * x * h.z⁻¹) = zpowers x
    rw [mem_centralizer_singleton_iff.mp hzC, mul_inv_cancel_right]
  have htN : t ∈ normalizer (zpowers x : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (t * x * t⁻¹) = zpowers x
    rw [htx, zpowers_inv]
  let zA : normalizer (A : Set G) := ⟨h.z, hNA hzN⟩
  let tA : normalizer (A : Set G) := ⟨t, hNA htN⟩
  let α : MulAut A := A.normalizerMonoidHom zA
  let β : MulAut A := A.normalizerMonoidHom tA
  have hz2 : zA * zA = 1 := by
    apply Subtype.ext
    change h.z * h.z = 1
    simpa only [h.involution, pow_two] using pow_orderOf_eq_one h.z
  have ht2 : tA * tA = 1 := by
    apply Subtype.ext
    change t * t = 1
    simpa only [ht, pow_two] using pow_orderOf_eq_one t
  have hα : α * α = 1 := by
    change A.normalizerMonoidHom zA * A.normalizerMonoidHom zA = 1
    rw [← map_mul, hz2, map_one]
  have hβ : β * β = 1 := by
    change A.normalizerMonoidHom tA * A.normalizerMonoidHom tA = 1
    rw [← map_mul, ht2, map_one]
  have hαfixed : Nat.card {a : A // α a = a} = 3 := by
    let e : {a : A // α a = a} ≃ (A ⊓ centralizer ({h.z} : Set G) : Subgroup G) :=
      { toFun := fun a => ⟨a, a.1.property, mem_centralizer_singleton_iff.mpr
          (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val a.property)).symm⟩
        invFun := fun a => ⟨⟨a, a.property.1⟩, by
          apply Subtype.ext
          change h.z * (a : G) * h.z⁻¹ = (a : G)
          rw [← mem_centralizer_singleton_iff.mp a.property.2, mul_inv_cancel_right]⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr e).trans hfixed
  let xA : A := ⟨x, hxA⟩
  have hxAo : orderOf xA = 3 :=
    (orderOf_injective A.subtype Subtype.val_injective xA).symm.trans hx
  have hβx : β xA = xA⁻¹ := Subtype.ext htx
  have hsum := MulAut.inverted_card_sum_of_cyclic_three_fifteen hcard α β hα hβ
    hαfixed xA hxAo hβx
  have hcβ : Nat.card {a : A // t * (a : G) * t⁻¹ = (a : G)⁻¹} =
      Nat.card {a : A // β a = a⁻¹} := by
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun _ =>
      ⟨fun he => Subtype.ext he, fun he => congrArg Subtype.val he⟩))
  have hcαβ : Nat.card {a : A // (h.z * t) * (a : G) * (h.z * t)⁻¹ = (a : G)⁻¹} =
      Nat.card {a : A // (α * β) a = a⁻¹} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro a
    constructor
    · intro he
      apply Subtype.ext
      change h.z * (t * (a : G) * t⁻¹) * h.z⁻¹ = (a : G)⁻¹
      simpa only [mul_inv_rev, mul_assoc] using he
    · intro he
      have he' := congrArg Subtype.val he
      change h.z * (t * (a : G) * t⁻¹) * h.z⁻¹ = (a : G)⁻¹ at he'
      simpa only [mul_inv_rev, mul_assoc] using he'
  have hn : zpowers h.z ≤ normalizer (A : Set G) := zpowers_le.mpr (hNA hzN)
  rw [Subgroup.inverting_count_eq_two_twisted_counts x h.z t hx h.involution ht
    (mem_centralizer_singleton_iff.mp htz).symm htx A hn hd hprod,
    hcβ, hcαβ, hsum]
  have hCcard : Nat.card (centralizer ({x} : Set G)) = 2 * Nat.card A := by
    rw [← hprod, card_sup_eq_mul_of_normalizes_of_disjoint A _ hn hd,
      Nat.card_zpowers, h.involution, Nat.mul_comm]
  rcases hcard with hcard | hcard <;> norm_num [hCcard, hcard]

end CFSG.Quasithin.Janko1CentralizerData
