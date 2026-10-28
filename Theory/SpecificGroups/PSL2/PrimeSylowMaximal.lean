module

public import Glauberman.DicksonClassification
public import GorensteinWalter.PSL2Cardinality
public import Mathlib.GroupTheory.Complement

/-!
# Maximal Sylow two-subgroups in prime-field PSL₂

If p is prime and p − 1 or p + 1 is a power of two at least sixteen,
every Sylow two-subgroup of PSL₂(p) is maximal. The order formula puts
that power of two in every Sylow overgroup. Dickson's classification
excludes the elementary abelian, cyclic, small alternating and symmetric,
and semidirect-product cases by their orders. The prime-field hypothesis
excludes proper subfield cases. In the remaining dihedral case the order
bound makes the overgroup a two-group, hence the original Sylow subgroup.

Source: Dickson's subgroup classification, Huppert, Endliche Gruppen I,
II.8.27, through the proved Glauberman.DicksonClassification interface.
This is the model calculation used in Aschbacher–Smith 2.3.9(7)(e).
-/

open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise

namespace Matrix.ProjectiveSpecialLinearGroup

private theorem adjacent_power_dvd_card {p k : ℕ} [Fact p.Prime]
    (hp : Odd p)
    (hpk : p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k) :
    2 ^ k ∣ Nat.card (PSL2MatrixGroup (ZMod p)) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hsub : 2 ∣ p - 1 := by
    rcases hp with ⟨a, ha⟩
    exact ⟨a, by omega⟩
  have hadd : 2 ∣ p + 1 := by
    rcases hp with ⟨a, ha⟩
    exact ⟨a + 1, by omega⟩
  have hcard := GorensteinWalter.psl2_card_formula (ZMod p)
    ⟨p, 1, Fact.out, hp, by omega, by simp⟩
  simp only [Nat.card_zmod] at hcard
  rw [hcard]
  have hsq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    nlinarith [Nat.sub_add_cancel (show 1 ≤ p by omega),
      Nat.sub_add_cancel (show 1 ≤ p ^ 2 by nlinarith)]
  rw [hsq]
  apply (Nat.dvd_div_iff_mul_dvd
    (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hsub _) _)).mpr
  apply dvd_mul_of_dvd_right
  rcases hpk with h | h
  · rw [h]
    rw [Nat.mul_comm (2 ^ k) (p + 1)]
    exact Nat.mul_dvd_mul hadd (dvd_refl _)
  · rw [h]
    exact Nat.mul_dvd_mul hsub (dvd_refl _)

/-- A proper subgroup containing a Sylow two-subgroup is a two-group when
one adjacent integer is a power of two at least sixteen. -/
private theorem proper_overgroup_sylow_two_isPGroup {p k : ℕ} [Fact p.Prime]
    (hk : 4 ≤ k) (hpk : p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k)
    (S : Sylow 2 (PSL2MatrixGroup (ZMod p)))
    (U : Subgroup (PSL2MatrixGroup (ZMod p)))
    (hSU : (S : Subgroup _) ≤ U) (hU : U ≠ ⊤) : IsPGroup 2 U := by
  classical
  have h16 : 16 ≤ 2 ^ k := by
    exact (show 2 ^ 4 ≤ 2 ^ k from Nat.pow_le_pow_right (by omega) hk)
  have hp7 : 7 < p := by rcases hpk with h | h <;> omega
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hgcd : Nat.gcd (p - 1) 2 = 2 := by
    apply Nat.gcd_eq_right
    rcases hpodd with ⟨a, ha⟩
    exact ⟨a, by omega⟩
  have hdivS : 2 ^ k ∣ Nat.card S :=
    S.pow_dvd_card_of_pow_dvd_card (adjacent_power_dvd_card hpodd hpk)
  have hdivU : 2 ^ k ∣ Nat.card U := hdivS.trans (Subgroup.card_dvd_of_le hSU)
  have h16U : 16 ∣ Nat.card U :=
    (pow_dvd_pow 2 hk).trans hdivU
  have hUpos : 0 < Nat.card U := Nat.card_pos
  have hhalf : (p + 1) / 2 < 2 ^ k := by rcases hpk with h | h <;> omega
  have hhalf' : (p - 1) / 2 < 2 ^ k := by omega
  have hpBound : p + 1 < 2 * 2 ^ k := by rcases hpk with h | h <;> omega
  have hcardF : Nat.card (ZMod p) = p ^ 1 := by simp
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      hcardF U with hEl | hCyc | hDih | hA4 | hS4 | hA5 | hSD | hPSL | hPGL
  · have hodd : Odd (Nat.card U) := by
      obtain ⟨a, ha⟩ := (IsElementaryAbelian.isPGroup p U).exists_card_eq
      rw [ha]
      exact hpodd.pow
    exact False.elim (hodd.not_two_dvd_nat ((by decide : 2 ∣ 16).trans h16U))
  · obtain ⟨n, hn, hcard, _⟩ := hCyc
    have hnpos : 0 < n := hcard ▸ hUpos
    have hnlow : 2 ^ k ≤ n := Nat.le_of_dvd hnpos (hcard ▸ hdivU)
    simp only [Nat.card_zmod, hgcd] at hn
    rcases hn with hn | hn
    · have := Nat.le_of_dvd (show 0 < (p - 1) / 2 by omega) hn
      omega
    · have := Nat.le_of_dvd (show 0 < (p + 1) / 2 by omega) hn
      omega
  · obtain ⟨n, hn, hcard, _⟩ := hDih
    simp only [Nat.card_zmod, hgcd] at hn
    have hbound : Nat.card U ≤ p + 1 := by
      rw [hcard]
      rcases hn with hn | hn
      · have := Nat.le_of_dvd (show 0 < (p - 1) / 2 by omega) hn
        omega
      · have := Nat.le_of_dvd (show 0 < (p + 1) / 2 by omega) hn
        omega
    have heq : Nat.card U = 2 ^ k :=
      Nat.eq_of_dvd_of_lt_two_mul hUpos.ne' hdivU (lt_of_le_of_lt hbound hpBound)
    exact IsPGroup.of_card heq
  · obtain ⟨e⟩ := hA4.2
    have hc : Nat.card U = 12 := by
      rw [Nat.card_congr e.toEquiv, alternatingGroup.card_of_card_eq_four (by simp)]
    rw [hc] at h16U
    norm_num at h16U
  · obtain ⟨e⟩ := hS4.2
    have hc : Nat.card U = 24 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm]
      norm_num [Nat.factorial]
    rw [hc] at h16U
    norm_num at h16U
  · obtain ⟨e⟩ := hA5.2
    have hc : Nat.card U = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
        Nat.card_eq_fintype_card]
      norm_num [Nat.factorial]
    rw [hc] at h16U
    norm_num at h16U
  · obtain ⟨a, c, _, hcdiv, N, C, hNnormal, hNelem, hNcard,
        hCcyc, hCcard, hdisj, hjoin⟩ := hSD
    let : N.Normal := hNnormal
    have hcomp : N.IsComplement' C := by
      refine ⟨Subgroup.mul_injective_of_disjoint hdisj, ?_⟩
      intro g
      have hg : (g : U) ∈ (N : Set U) * (C : Set U) := by
        rw [← Subgroup.normal_mul N C, hjoin]
        trivial
      obtain ⟨n, hn, c, hc, heq⟩ := hg
      exact ⟨⟨⟨n, hn⟩, ⟨c, hc⟩⟩, heq⟩
    have hcU : p ^ a * c = Nat.card U := by
      simpa only [hNcard, hCcard] using hcomp.card_mul_card
    have hcop : Nat.Coprime (2 ^ k) (p ^ a) :=
      (Nat.coprime_two_left.mpr hpodd).pow k a
    have hdc : 2 ^ k ∣ c := hcop.dvd_of_dvd_mul_left (hcU ▸ hdivU)
    have hcpos : 0 < c := by
      rw [← hCcard]
      exact Nat.card_pos
    have hclow := Nat.le_of_dvd hcpos hdc
    simp only [pow_one, hgcd] at hcdiv
    have hcup := Nat.le_of_dvd (show 0 < (p - 1) / 2 by omega) hcdiv
    omega
  · obtain ⟨m, hm, hmdiv, ⟨e⟩⟩ := hPSL
    have hm1 : m = 1 := Nat.eq_one_of_dvd_one hmdiv
    subst m
    have hK : Nat.card (GaloisField p 1) = p := by
      simpa using GaloisField.card p 1 (by decide)
    have hc : Nat.card U = Nat.card (PSL2MatrixGroup (ZMod p)) := by
      rw [Nat.card_congr e.toEquiv,
        GorensteinWalter.psl2_card_formula (GaloisField p 1)
          ⟨p, 1, Fact.out, hpodd, by omega, by simpa using hK⟩,
        GorensteinWalter.psl2_card_formula (ZMod p)
          ⟨p, 1, Fact.out, hpodd, by omega, by simp⟩, hK, Nat.card_zmod]
    exact False.elim (hU (U.eq_top_of_card_eq hc))
  · obtain ⟨m, hm, hmdiv, _⟩ := hPGL
    have := Nat.le_of_dvd (by decide : 0 < 1) hmdiv
    omega

/-- Sylow two-subgroups are maximal for these prime-field parameters. -/
public theorem sylow_two_isCoatom_of_adjacent_power {p k : ℕ} [Fact p.Prime]
    (hk : 4 ≤ k) (hpk : p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k)
    (S : Sylow 2 (PSL2MatrixGroup (ZMod p))) : IsCoatom (S : Subgroup (PSL2MatrixGroup (ZMod p))) := by
  have h16 : 16 ≤ 2 ^ k :=
    (show 2 ^ 4 ≤ 2 ^ k from Nat.pow_le_pow_right (by omega) hk)
  have hp7 : 7 < p := by rcases hpk with h | h <;> omega
  have hp : p.Prime := Fact.out
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have heven : 2 ∣ p ^ 2 - 1 := by
    obtain ⟨a, ha⟩ := hpodd
    refine ⟨2 * a * (a + 1), ?_⟩
    nlinarith [Nat.sub_add_cancel (show 1 ≤ p ^ 2 by nlinarith)]
  have hpdiv : p ∣ Nat.card (PSL2MatrixGroup (ZMod p)) := by
    rw [GorensteinWalter.psl2_card_formula (ZMod p)
      ⟨p, 1, hp, hpodd, by omega, by simp⟩, Nat.card_zmod]
    apply (Nat.dvd_div_iff_mul_dvd (dvd_mul_of_dvd_right heven p)).mpr
    simpa only [Nat.mul_comm] using Nat.mul_dvd_mul (dvd_refl p) heven
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨?_, ?_⟩
  · intro htop
    have hpS : p ∣ Nat.card S := by simpa only [htop, Subgroup.card_top] using hpdiv
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn] at hpS
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hpS
    have := Nat.le_of_dvd (by decide : 0 < 2) hp2
    omega
  · intro U hU hSU
    exact le_of_eq (S.is_maximal'
      (proper_overgroup_sylow_two_isPGroup hk hpk S U hSU hU) hSU)

end Matrix.ProjectiveSpecialLinearGroup
