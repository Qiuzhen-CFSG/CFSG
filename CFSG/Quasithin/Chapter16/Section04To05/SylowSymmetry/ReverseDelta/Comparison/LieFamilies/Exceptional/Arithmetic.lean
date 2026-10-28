module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Actions
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.Divisibility

/-!
# Odd divisibility through the two central kernels

An odd divisor survives a two-group kernel and passage to O². Applying this
separately to both actual central-image maps transports every odd divisor
of the outer residual to the inner fixed subgroup. A bound on the latter's
odd part then gives a contradiction. Neither central image is identified
with the other. The two elementary inequalities are the G₂ and genuine
triality half-field comparisons.

Source: Aschbacher--Smith, proof of 16.4.11(2), printed p.1193, using
16.1.2--4, pp.1170--1171, combined manuscript (1 March 2004).
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Exceptional
open Subgroup Theory.GroupTheory

theorem odd_dvd_residual_iff {H : Type*} [Group H] [Finite H]
    {n : ℕ} (hn : Odd n) : n ∣ Nat.card (pResidual 2 H) ↔ n ∣ Nat.card H := by
  constructor
  · exact fun h => h.trans (card_subgroup_dvd_card _)
  · intro h
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_quotient_pResidual (G := H) 2)
    have hc := (pResidual 2 H).card_mul_index
    rw [index_eq_card, hk] at hc
    exact ((hn.coprime_two_right.pow_right k).dvd_mul_right).mp (hc ▸ h)

theorem odd_dvd_centralImage_iff {G : Type*} [Group G] [Finite G]
    {L X : Subgroup G} [IsQuasisimple L] (hodd : pPrimeCore 2 L = ⊥)
    (hXL : X ≤ L) {n : ℕ} (hn : Odd n) :
    n ∣ Nat.card (centralImage L X) ↔ n ∣ Nat.card X := by
  let f := centralImageMap hXL
  have hf := centralImageMap_surjective hXL
  constructor
  · exact fun h => h.trans (card_dvd_of_surjective f hf)
  · intro h
    have hc : Nat.card f.ker * Nat.card (centralImage L X) = Nat.card X := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
      exact f.ker.card_mul_index
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      (OtherFamilies.centralImageMap_two_kernel hodd hXL)
    rw [hk] at hc
    exact ((hn.coprime_two_right.pow_right k).dvd_mul_left).mp (hc ▸ h)

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

theorem outer_odd_dvd_inner_fixed (d : Contrary T z L g R r)
    {S : Type*} [Group S] [Finite S] (e : (L ⧸ center L) ≃* S)
    {n : ℕ} (hn : Odd n)
    (ho : n ∣ Nat.card (pResidual 2 (outerAction d e).fixedSubgroup)) :
    n ∣ Nat.card (innerAction d e).fixedSubgroup := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let : IsQuasisimple (L.conjBy g) :=
    IsQuasisimple.of_mulEquiv ((MulAut.conj g).subgroupMap L)
  have hY : n ∣ Nat.card (residual (L.conjBy g) z) :=
    (odd_dvd_centralImage_iff (conjugate_oddCore d)
      ((residual_le (L.conjBy g) z).trans inf_le_left) hn).mp
      ((Nat.card_congr (outerResidualEquiv d e).toEquiv).symm ▸ ho)
  have hX : n ∣ Nat.card (centralImage L (residual L r)) :=
    (odd_dvd_centralImage_iff (component_oddCore d)
      ((residual_le L r).trans inf_le_left) hn).mpr
      (hY.trans (card_dvd_of_le d.residual_normal.1))
  rw [Nat.card_congr (innerResidualEquiv d e).toEquiv] at hX
  exact hX.trans (card_subgroup_dvd_card _)

theorem false_of_odd_bound (d : Contrary T z L g R r)
    {S : Type*} [Group S] [Finite S] (e : (L ⧸ center L) ≃* S)
    {n b : ℕ} (hn : Odd n) (hb : 0 < b) (hlt : b < n)
    (hi : ∃ k : ℕ, Nat.card (innerAction d e).fixedSubgroup ∣ 2 ^ k * b)
    (ho : n ∣ Nat.card (pResidual 2 (outerAction d e).fixedSubgroup)) : False := by
  obtain ⟨k, hk⟩ := hi
  have hdiv := (outer_odd_dvd_inner_fixed d e hn ho).trans hk
  have hnb : n ∣ b := ((hn.coprime_two_right.pow_right k).dvd_mul_left).mp hdiv
  exact (Nat.not_le_of_gt hlt) (Nat.le_of_dvd hb hnb)

theorem binary_power_sub_one_odd {m : ℕ} (hm : 0 < m) {k : ℕ} (hk : 0 < k) :
    Odd ((2 ^ m) ^ k - 1) := by
  have hp : Even ((2 ^ m) ^ k) :=
    (even_two.pow_of_ne_zero (Nat.ne_of_gt hm)).pow_of_ne_zero (Nat.ne_of_gt hk)
  have hpos : 1 ≤ (2 ^ m) ^ k := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by decide))
  exact Nat.Even.sub_odd hpos hp (by decide)

theorem g2_odd_bound {q : ℕ} (hq : 2 ≤ q) : q ^ 4 - 1 < q ^ 6 - 1 := by
  have hlt : q ^ 4 < q ^ 6 := Nat.pow_lt_pow_right (by omega) (by decide)
  have hpos : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  omega

theorem triality_odd_bound {q : ℕ} (hq : 2 ≤ q) :
    q ^ 12 - 1 < (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) := by
  have hp : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hid : q ^ 12 - 1 = (q ^ 8 + q ^ 4 + 1) * (q ^ 4 - 1) := by
    have he : (q ^ 8 + q ^ 4 + 1) * (q ^ 4 - 1) + 1 = q ^ 12 := by
      calc
        _ = (q ^ 8 + q ^ 4 + 1) * q ^ 4 - (q ^ 8 + q ^ 4 + 1) + 1 := by
          rw [Nat.mul_sub, mul_one]
        _ = q ^ 12 := by
          have hr : (q ^ 8 + q ^ 4 + 1) * q ^ 4 = q ^ 12 + q ^ 8 + q ^ 4 := by ring
          rw [hr]
          have : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ (by omega)
          omega
    omega
  rw [hid]
  exact Nat.mul_lt_mul_of_pos_left (g2_odd_bound hq) (by omega)

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Exceptional
