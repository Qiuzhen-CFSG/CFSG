module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.SporadicModels
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage.Stabilizers
public import Theory.Mathieu.M22.Properties.InvolutionFixedOrders
public import Theory.Mathieu.M22.Properties.FixedHexads
public import Mathlib.GroupTheory.GroupAction.Primitive
/-!
# The exceptional section cannot be Sylow-normalized in M₂₂

A quotient of order 20160 forces the original two-core to have order at
most two. If it has order two, its involution centralizes the original
subgroup, contradicting the checked absence of a factor nine in every
involutory fixed subgroup of M₂₂. Otherwise the subgroup has index22.
The intrinsic index22 classification identifies it with a natural point
stabilizer, and primitivity makes it self-normalizing. Its order has
smaller two-part than the ambient full Sylow, a contradiction.

The proof uses the literal subgroup, quotient and normalization maps.
It applies to each exceptional source seed, including PSL₃(4), without
identifying that carrier with the different group PSL₄(2) of equal order.
Source: Aschbacher–Smith A.3.12(12), printed p.47, as used in13.6.27, p.934.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
private theorem m22_core_card_dvd_two (B : Subgroup M22)
    (hq : Nat.card (B ⧸ pCore 2 B) = 20160) : Nat.card (pCore 2 B) ∣ 2 := by
  have hd := B.card_subgroup_dvd_card
  rw [m22_order, ← (pCore 2 B).card_mul_index,
    show (pCore 2 B).index = 20160 from hq] at hd
  have hd' : Nat.card (pCore 2 B) ∣ 2 * 11 :=
    (Nat.mul_dvd_mul_iff_right (by decide : 0 < 20160)).mp hd
  have hc : Nat.Coprime (Nat.card (pCore 2 B)) 11 := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 11).pow_left n
  exact hc.dvd_of_dvd_mul_right hd'

private theorem m22_core_eq_bot (B : Subgroup M22)
    (hq : Nat.card (B ⧸ pCore 2 B) = 20160) : pCore 2 B = ⊥ := by
  by_contra hc
  have hcard : Nat.card (pCore 2 B) = 2 :=
    ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp (m22_core_card_dvd_two B hq)).resolve_left
      (fun h1 => hc ((pCore 2 B).eq_bot_iff_card.mpr h1))
  let U := (pCore 2 B).map B.subtype
  have hU : Nat.card U = 2 := (card_map_of_injective B.subtype_injective).trans hcard
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  have hzG : orderOf (z : M22) = 2 := (orderOf_coe z).trans hz
  have heq : zpowers (z : M22) = U := eq_of_le_of_card_ge
    (zpowers_le.mpr z.property) (by rw [Nat.card_zpowers,hzG,hU])
  have hBN : B ≤ normalizer (U : Set M22) :=
    B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  rw [← heq, normalizer_zpowers_eq_centralizer_of_order_two _ hzG] at hBN
  let r := MulAut.conj (z : M22)
  have hr : orderOf r = 2 :=
    (orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot) z).trans hzG
  have hBr : B ≤ r.fixedSubgroup := by
    intro b hb
    apply (MulAut.mem_fixedSubgroup r b).mpr
    change (z : M22) * b * (z : M22)⁻¹ = b
    have hcomm := mem_centralizer_singleton_iff.mp (hBN hb)
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hd : 9 ∣ Nat.card B := by
    exact (by decide : 9 ∣ 20160).trans (hq ▸ card_quotient_dvd_card (pCore 2 B))
  exact m22_involution_not_nine_dvd_fixed_card r hr (hd.trans (card_dvd_of_le hBr))

private theorem m22_not_section_card (S : Sylow 2 M22) (B : Subgroup M22)
    (hn : (S : Subgroup M22) ≤ normalizer (B : Set M22))
    (hq : Nat.card (B ⧸ pCore 2 B) = 20160) : False := by
  have hc := m22_core_eq_bot B hq
  have hBcard : Nat.card B = 20160 := by
    have hh : (pCore 2 B).index = 20160 := hq
    simpa only [hc, index_bot] using hh
  have hi : B.index = 22 := by
    have hh := B.card_mul_index
    rw [hBcard, m22_order] at hh
    omega
  obtain ⟨y, hy⟩ := m22_index_twenty_two_eq_stabilizer B hi
  let := m22_isPreprimitive
  let := m22_isSimpleGroup
  have hmax : IsCoatom B := by
    rw [hy]
    exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive M22 y
  have hproper : normalizer (B : Set M22) ≠ ⊤ := by
    intro ht
    have : B.Normal := normalizer_eq_top_iff.mp ht
    rcases (inferInstance : B.Normal).eq_bot_or_eq_top with he | he
    · rw [he, card_bot] at hBcard
      omega
    · exact hmax.ne_top he
  have hnorm : normalizer (B : Set M22) = B :=
    (hmax.le_iff_eq hproper).mp B.le_normalizer
  have hd : Nat.card S ∣ Nat.card B := card_dvd_of_le (hn.trans (le_of_eq hnorm))
  have hs : Nat.card S = 128 := by
    rw [S.card_eq_multiplicity, m22_order]
    decide +kernel
  rw [hs, hBcard] at hd
  norm_num at hd

variable {G : Type*} [Group G] [Finite G]

/-- A full-Sylow-normalized subgroup of M₂₂ cannot have a two-core
quotient of order 20160. -/
theorem not_mathieu_twentyTwo_of_section_card
    (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hq : Nat.card (B ⧸ pCore 2 B) = 20160)
    (e : G ≃* Sporadic.Mathieu.M22) : False := by
  let eB := e.subgroupMap B
  let q := QuotientGroup.congr (pCore 2 B) (pCore 2 (B.map e.toMonoidHom)) eB
    (pCore_map_iso 2 eB)
  have hm : Nat.card ((B.map e.toMonoidHom) ⧸ pCore 2 (B.map e.toMonoidHom)) = 20160 :=
    (Nat.card_congr q.symm.toEquiv).trans hq
  exact m22_not_section_card (S.mapSurjective e.surjective) (B.map e.toMonoidHom)
    ((map_mono hn).trans (le_normalizer_map e.toMonoidHom)) hm

/-- None of the three exceptional source sections can occur in the
M₂₂ containing row under the original full Sylow normalization. -/
theorem not_mathieu_twentyTwo
    (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : IsModel (B ⧸ pCore 2 B)) (e : G ≃* Sporadic.Mathieu.M22) : False := by
  have hd : Nat.card (B ⧸ pCore 2 B) ∣ Nat.card G :=
    (card_quotient_dvd_card _).trans B.card_subgroup_dvd_card
  rw [Nat.card_congr e.toEquiv, m22_order] at hd
  rcases h.card with hj | hm | hl
  · rw [hj] at hd
    norm_num at hd
  · rw [hm] at hd
    norm_num at hd
  · exact not_mathieu_twentyTwo_of_section_card S B hn hl e

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
