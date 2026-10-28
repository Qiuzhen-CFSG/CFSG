module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter.CardBounds
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.SpecificGroups.Tits.FiniteSimple
public import BenderSuzuki.SE.Section11Lemma115Endpoint

/-!
# The small and rank-one characteristic-two comparisons

An odd-prime PSL₂ isomorphic to binary PSL₂ has parameter five: prime
factor divisibility first forces p = q+1, and the two orders force q = 4.
The order-168 binary PSL₃ overlap similarly retains p = 7. The binary
linear groups, actual derived symplectic and octonion carriers, and actual
Tits presentation have incompatible orders. Suzuki groups are excluded
because their order is prime to three.

Every comparison transports order through an actual model equivalence.
The small-derived equivalences and order facts are proved in the imported
modules; no exceptional isomorphism is assumed. Source: Aschbacher–Smith,
full 1.1.5(3), printed pp.501–503, and the proof of 15.4.20, p.1164.
ATLAS attribution and license are preserved in the imported order modules.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter
variable {Q : Type*} [Group Q]

/-- The only odd-prime PSL₂ isomorphic to a binary PSL₂ is PSL₂(5). -/
theorem linear_two_odd_parameter {p f : ℕ} (hp : p.Prime) (ho : Odd p)
    (hp5 : 5 ≤ p) (hf : 2 ≤ f) (hodd : ClassicalGroup.IsPSL Q 2 p)
    (hbinary : ClassicalGroup.IsPSL Q 2 (2^f)) : p = 5 := by
  let q := 2^f
  have hq4 : 4 ≤ q := by simpa [q] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hf
  have hqe : Even q := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega : f ≠ 0))
  have hqc : Nat.Coprime 2 (q-1) := Nat.coprime_two_left.mpr (by
    obtain ⟨k,hk⟩ := hqe
    exact ⟨k-1, by omega⟩)
  have hc : Nat.card Q = q * (q^2-1) := by
    have hh := psl_two_card_mul hbinary
    change Nat.card Q * Nat.gcd 2 (q-1) = q*(q^2-1) at hh
    simpa only [hqc.gcd_eq_one, mul_one] using hh
  have he := odd_card_twice ho hodd
  rw [hc] at he
  have hqsub : q^2-1+1=q^2 := Nat.sub_add_cancel (by nlinarith)
  have hpsub : p^2-1+1=p^2 := Nat.sub_add_cancel (by nlinarith)
  have hqp : q < p := by
    by_contra hn
    have hle : p ≤ q := by omega
    have hm := Nat.mul_le_mul hle
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hle 2) 1)
    nlinarith
  have hpd : p ∣ q*(q^2-1) := by
    have hd : p ∣ (q*(q^2-1))*2 := he ▸ dvd_mul_right p (p^2-1)
    exact ((hp.coprime_iff_not_dvd.mpr (by
      intro hd
      have := Nat.le_of_dvd (by decide : 0 < 2) hd
      omega)).dvd_mul_right).mp hd
  have hpnq : ¬ p ∣ q := by
    intro hd
    have hd2 := hp.dvd_of_dvd_pow hd
    have := Nat.le_of_dvd (by decide : 0 < 2) hd2
    omega
  have hfac : q^2-1 = (q-1)*(q+1) := by
    have hqsub' : q-1+1=q := Nat.sub_add_cancel (by omega)
    nlinarith
  have hpd' := (hp.dvd_mul.mp hpd).resolve_left hpnq
  rw [hfac] at hpd'
  have hple : p ≤ q+1 := by
    rcases hp.dvd_mul.mp hpd' with hd | hd
    · have := Nat.le_of_dvd (by omega : 0 < q-1) hd
      omega
    · exact Nat.le_of_dvd (by omega) hd
  have hpq : p = q+1 := by omega
  have he' : q = 4 := by
    subst p
    nlinarith [sq_nonneg (q-4)]
  omega

/-- The order-168 binary rank-three overlap retains the parameter seven. -/
theorem linear_three_two_odd_parameter {p : ℕ} (ho : Odd p)
    (hodd : ClassicalGroup.IsPSL Q 2 p) (hbinary : ClassicalGroup.IsPSL Q 3 2) :
    p = 7 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hbinary
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [← Nat.card_congr e.toEquiv, hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  have he := odd_card_twice ho hodd
  rw [show Nat.card Q = 168 by omega] at he
  have hp8 : p < 8 := by
    by_contra hn
    have hp : 8 ≤ p := by omega
    have hm := Nat.mul_le_mul hp
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hp 2) 1)
    norm_num at hm
    omega
  interval_cases p <;> norm_num at *

/-- Neither binary linear model of degrees four and five is a PSL₂. -/
theorem not_binary_linear {p n : ℕ} (hn : n = 4 ∨ n = 5)
    (hodd : ClassicalGroup.IsPSL Q 2 p) (hbinary : ClassicalGroup.IsPSL Q n 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hbinary
  rcases hn with rfl | rfl
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    rw [← Nat.card_congr e.toEquiv, hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
    exact psl_two_card_ne_20160 hodd (by omega)
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    rw [← Nat.card_congr e.toEquiv, hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
    exact psl_two_card_ne_of_gaps (c := 9999360) (a := 215) (b := 271) hodd
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by omega)

/-- The actual derived projective symplectic endpoint has order 360. -/
theorem not_symplectic_derived {p : ℕ} (hp : p.Prime)
    (hodd : ClassicalGroup.IsPSL Q 2 p)
    (hmodel : Nonempty (Q ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) : False := by
  obtain ⟨e⟩ := hmodel
  have hc := Nat.card_congr (e.trans
    Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv
  rw [nat_card_alternatingGroup] at hc
  norm_num at hc
  have he := parameter_nine_of_card_360 hodd hc
  rw [he] at hp
  norm_num at hp

/-- The actual derived octonion endpoint has order 6048. -/
theorem not_g2_derived {p : ℕ} (hodd : ClassicalGroup.IsPSL Q 2 p)
    (hmodel : Nonempty (Q ≃* commutator (Atlas.G2.Model (ZMod 2)))) : False := by
  obtain ⟨e⟩ := hmodel
  have hc := Nat.card_congr e.toEquiv
  rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
    Atlas.G2.BinaryException.card_H] at hc
  exact psl_two_card_ne_of_gaps (c := 6048) (a := 18) (b := 22) hodd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc

/-- Parrott's actual Tits presentation has incompatible order. -/
theorem not_tits {p : ℕ} (hodd : ClassicalGroup.IsPSL Q 2 p)
    (hmodel : Nonempty (Q ≃* Tits.ParrottGroup)) : False := by
  obtain ⟨e⟩ := hmodel
  have hc := (Nat.card_congr e.toEquiv).trans Tits.parrottGroup_card
  exact psl_two_card_ne_of_gaps (c := 17971200) (a := 261) (b := 330) hodd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc

private theorem three_dvd_psl_two {p : ℕ} (ho : Odd p)
    (hodd : ClassicalGroup.IsPSL Q 2 p) : 3 ∣ Nat.card Q := by
  have hp2 : 2 ≤ p := by
    obtain ⟨F,_,_,hF,_⟩ := hodd
    have hh := Finite.one_lt_card (α := F)
    omega
  have hsub : p^2-1+1=p^2 := Nat.sub_add_cancel (by nlinarith)
  have hd : 3 ∣ p*(p^2-1) := by
    have hr : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    have hs := Nat.pow_mod p 2 3
    have hm := Nat.mul_mod p (p^2-1) 3
    rcases hr with hr | hr | hr <;> rw [hr] at hs hm <;>
      norm_num at hs hm <;> omega
  rw [← odd_card_twice ho hodd] at hd
  exact (Nat.prime_three.dvd_mul.mp hd).resolve_right (by decide)

/-- Suzuki's three-free order excludes an odd PSL₂ model. -/
theorem not_suzuki {p m : ℕ} (ho : Odd p) (hm : 1 ≤ m)
    (hodd : ClassicalGroup.IsPSL Q 2 p)
    (hmodel : Nonempty (Q ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) : False := by
  obtain ⟨e⟩ := hmodel
  have hd := three_dvd_psl_two ho hodd
  rw [Nat.card_congr e.toEquiv,
    BenderSuzuki.lemma115_suzukiMatrixGroup_card_formula m (by omega)] at hd
  let q := 2^(2*m+1)
  have hqmod : q % 3 = 2 := by
    have hfour : 4^m % 3 = 1 := by
      change Nat.ModEq 3 (4^m) 1
      simpa only [one_pow] using (show Nat.ModEq 3 4 1 by decide).pow m
    have he : q = 2*4^m := by dsimp [q]; rw [pow_add, pow_mul]; ring
    rw [he, Nat.mul_mod, hfour]
  have hq2 : 2 ≤ q := Nat.le_pow (by omega : 0 < 2*m+1)
  have hsq : q^2 % 3 = 1 := by rw [Nat.pow_mod, hqmod]
  change 3 ∣ (q^2+1)*q^2*(q-1) at hd
  rcases Nat.prime_three.dvd_mul.mp hd with hd | hd
  · rcases Nat.prime_three.dvd_mul.mp hd with hd | hd <;> omega
  · omega

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter
