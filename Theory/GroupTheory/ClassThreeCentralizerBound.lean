module
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic

/-!
# Centralizer bounds from commutator images modulo the center

Let a group of order 512 have derived subgroup D=Z₂ of order 32.
If b lies outside D and |C_D(b)|=16, then an order greater than 64
for C_G(b) forces the commutator image of b in G/Z(G) to have order two.
The commutator homomorphism G→G/Z(G) has kernel containing C_G(b)D,
whose order is twice |C_G(b)|. Its image is nontrivial because b is
outside Z₂. The group order then leaves only an image of order two.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674, property (d), expressed through the central quotient.
-/

namespace Subgroup
open scoped commutatorElement

private def centralCommutatorHom {Q : Type*} [Group Q]
    (hc : _root_.commutator Q ≤ center Q) (b : Q) : Q →* Q where
  toFun x := ⁅b, x⁆
  map_one' := by simp
  map_mul' x y := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hcent := mem_center_iff.mp (hc (commutator_mem_commutator (mem_top b) (mem_top y))) x
    calc
      _ = ⁅b,x⁆ * (x * ⁅b,y⁆) * x⁻¹ := by group
      _ = ⁅b,x⁆ * ⁅b,y⁆ := by rw [hcent]; group

private theorem centralCommutatorHom_range {Q : Type*} [Group Q]
    (hc : _root_.commutator Q ≤ center Q) (b : Q) :
    (centralCommutatorHom hc b).range = ⁅zpowers b, (⊤ : Subgroup Q)⁆ := by
  let f := centralCommutatorHom hc b
  have hcentral : f.range ≤ center Q := by
    rintro _ ⟨x, rfl⟩
    exact hc (commutator_mem_commutator (mem_top b) (mem_top x))
  let : f.range.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hcentral hx) g, mul_inv_cancel_right]
    exact hx⟩
  let π := QuotientGroup.mk' f.range
  have hb (x : Q) : Commute (π b) (π x) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact commutator_mem_commutator (mem_zpowers b) (mem_top x)
  · apply commutator_le.mpr
    intro y hy x _
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    apply (QuotientGroup.eq_one_iff _).mp
    change π ⁅b ^ n, x⁆ = 1
    rw [map_commutatorElement, map_zpow]
    exact commutatorElement_eq_one_iff_mul_comm.mpr ((hb x).zpow_left n).eq

/-- With the fixed subgroup of order sixteen, excluding an order-two
commutator image in the central quotient bounds the centralizer by 64. -/
public theorem centralizer_card_le_sixty_four_of_quotient_commutator_not_two
    {V : Type*} [Group V] [Finite V]
    (hcard : Nat.card V = 512) (hDcard : Nat.card (_root_.commutator V) = 32)
    (hUpper : _root_.commutator V = Subgroup.upperCentralSeries V 2)
    (b : V) (hb : b ∉ _root_.commutator V)
    (hfixed : Nat.card (_root_.commutator V ⊓ centralizer ({b} : Set V) : Subgroup V) = 16)
    (hline : Nat.card ↥(⁅zpowers (QuotientGroup.mk' (center V) b),
      (⊤ : Subgroup (V ⧸ center V))⁆) ≠ 2) :
    Nat.card (centralizer ({b} : Set V)) ≤ 64 := by
  let Q := V ⧸ center V
  let q := QuotientGroup.mk' (center V)
  let D := _root_.commutator V
  let C := centralizer ({b} : Set V)
  have hDcentral : D ≤ (center Q).comap q := by
    rw [show D = Subgroup.upperCentralSeries V 2 from hUpper,
      ← Subgroup.comap_upperCentralSeries_quotient_center 1, Subgroup.upperCentralSeries_one]
  have hQcentral : _root_.commutator Q ≤ center Q := by
    have hm : D.map q = _root_.commutator Q := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
      rfl
    rw [← hm]
    exact map_le_iff_le_comap.mpr hDcentral
  let f : V →* Q := (centralCommutatorHom hQcentral (q b)).comp q
  have hrange : f.range = ⁅zpowers (q b), (⊤ : Subgroup Q)⁆ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
      ← MonoidHom.range_eq_map]
    exact centralCommutatorHom_range hQcentral (q b)
  have hker : D ⊔ C ≤ f.ker := by
    apply sup_le
    · intro d hd
      change ⁅q b, q d⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_center_iff.mp (hDcentral hd) (q b))
    · intro c hc
      change ⁅q b, q c⁆ = 1
      rw [← map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_centralizer_singleton_iff.mp hc).symm, map_one]
  have hprod : 2 * Nat.card C = Nat.card (D ⊔ C : Subgroup V) := by
    have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes D C
      (le_normalizer_of_normal (H := D))
    change Nat.card D = 32 at hDcard
    change Nat.card (D ⊓ C : Subgroup V) = 16 at hfixed
    rw [hDcard, hfixed] at hc
    omega
  have hkerbound : 2 * Nat.card C ≤ Nat.card f.ker := by
    rw [hprod]
    exact card_le_of_le hker
  have hnontriv : f.range ≠ ⊥ := by
    intro hbot
    apply hb
    rw [hUpper, ← Subgroup.comap_upperCentralSeries_quotient_center 1,
      Subgroup.upperCentralSeries_one]
    change q b ∈ center Q
    apply mem_center_iff.mpr
    intro x
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (center V) x
    have hone : f v = 1 := mem_bot.mp (hbot ▸ (show f v ∈ f.range from ⟨v, rfl⟩))
    exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
  have hrangecard : 4 ≤ Nat.card f.range := by
    have hdvd : Nat.card f.range ∣ 2 ^ 9 := by
      simpa only [hcard, show (2 : ℕ)^9 = 512 by decide] using card_range_dvd f
    obtain ⟨n, _, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hn0 : n ≠ 0 := by
      intro hn0
      exact hnontriv (card_eq_one.mp (by simpa only [hn0, pow_zero] using hn))
    have hn1 : n ≠ 1 := by
      intro hn1
      apply hline
      rw [← hrange]
      simpa only [hn1, pow_one] using hn
    rw [hn]
    exact (show 4 = 2 ^ 2 by decide) ▸ Nat.pow_le_pow_right (by decide) (by omega)
  have htotal := f.ker.index_mul_card
  rw [index_ker, hcard] at htotal
  have hbound := Nat.mul_le_mul hrangecard hkerbound
  rw [htotal] at hbound
  change Nat.card C ≤ 64
  omega

end Subgroup
