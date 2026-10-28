module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.CoreGrowth.Actions
public import Mathlib.Data.Nat.GCD.Basic

/-!
# The core order and actual complement in Lemma 15.3

The free torus action on V minus A makes |V| a power of q. For any odd
prime p dividing |J|, the commuting K×C_p action makes p divide |V|−q,
while the preceding cyclicity argument makes p coprime to q−1. Since
A<V, the next possible size q² is excluded. Thus |V|≥q³. The exact index
[M:D]=q³ and V∩D=1 force V to be a normal complement to D in M.

Source: GLS IV, Chapter 2, Lemma 15.3, final paragraph,
`refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII
universe u

private theorem power_of_binary_power_sub_dvd {n e : ℕ}
    (_hn : 0 < n) (hne : n ≤ e) (hd : 2 ^ n - 1 ∣ 2 ^ e - 2 ^ n) :
    ∃ k : ℕ, e = n * k := by
  have hpowle : 2 ^ n ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) hne
  have hadd : (2 ^ e - 2 ^ n) + (2 ^ n - 1) = 2 ^ e - 1 := by
    have hq := Nat.one_le_two_pow (n := n)
    omega
  have hdiv : 2 ^ n - 1 ∣ 2 ^ e - 1 := hadd ▸ dvd_add hd (dvd_refl _)
  have hmod := Nat.mod_eq_zero_of_dvd hdiv
  rw [Nat.pow_sub_one_mod_pow_sub_one] at hmod
  have hone : 2 ^ (e % n) = 1 := by
    have hp : 0 < 2 ^ (e % n) := pow_pos (by decide) _
    omega
  have hzero : e % n = 0 :=
    (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))) (by simpa using hone)
  exact Nat.dvd_of_mod_eq_zero hzero

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d
local notation "A" => closure (Z ∩ (M : Set G))
local notation "D" => residualPairStabilizer M t
local notation "J" => centralizer (residualGenerated M z t : Set G)
local notation "V" => Subgroup.map M.subtype (pCore 2 M)

/-- The source two-core has order at least q³ under the contrary hypothesis. -/
public theorem Context.point_twoCore_card_lower_of_involutions
    (hinv : ∀ v ∈ V, PFAppendixIII.IsInvolution v → v ∈ A) (hlt : A < V)
    (hnot : ¬ IsPGroup 2 J) : (2 ^ n) ^ 3 ≤ Nat.card V := by
  have hbad : ¬ (Nat.card J).primeFactors ⊆ (2 : ℕ).primeFactors :=
    fun hh => hnot ((isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr hh)
  obtain ⟨p, hpJ, hp2⟩ := Finset.not_subset.mp hbad
  obtain ⟨hp, hpd, _⟩ := Nat.mem_primeFactors.mp hpJ
  have hpne : p ≠ 2 := by
    intro he
    apply hp2
    subst p
    norm_num
  have hpodd := hp.odd_of_ne_two hpne
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := J) p hpd
  have hyG : orderOf (y : G) = p := (orderOf_coe y).trans hy
  obtain ⟨hcop, hd⟩ := d.torus_centralizer_product_arithmetic hinv hlt
    (zpowers (y : G)) (zpowers_le.mpr y.property) inferInstance
    (by rw [Nat.card_zpowers, hyG]; exact hpodd)
  rw [Nat.card_zpowers, hyG] at hcop hd
  have hV : IsPGroup 2 V := (pCore_isPGroup (p := 2) (G := M)).map M.subtype
  obtain ⟨e, he⟩ := hV.exists_card_eq
  have hqlt : 2 ^ n < Nat.card V := by
    rw [← d.distinguished_elementary_card.2]
    have hle := card_le_of_le hlt.le
    by_contra h
    exact hlt.ne (eq_of_le_of_card_ge hlt.le (by omega))
  have hne : n ≤ e := by
    have hh : 2 ^ n ≤ 2 ^ e := he ▸ hqlt.le
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hh
  have htor : 2 ^ n - 1 ∣ 2 ^ e - 2 ^ n :=
    he ▸ (dvd_mul_right (2 ^ n - 1) p).trans hd
  obtain ⟨k, hk⟩ := power_of_binary_power_sub_dvd (by have := d.parameter; omega) hne htor
  have hkcard : Nat.card V = (2 ^ n) ^ k := by rw [he, hk, pow_mul]
  have hkgt : 1 < k := by
    by_contra h
    have hkp : (2 ^ n) ^ k ≤ (2 ^ n) ^ 1 :=
      Nat.pow_le_pow_right (by positivity) (by omega)
    rw [← hkcard, pow_one] at hkp
    omega
  have hkn2 : k ≠ 2 := by
    intro hk2
    have hpdiv : p ∣ Nat.card V - 2 ^ n := (dvd_mul_left p (2 ^ n - 1)).trans hd
    have hdiff : (2 ^ n) ^ 2 - 2 ^ n = 2 ^ n * (2 ^ n - 1) := by
      rw [Nat.mul_sub_left_distrib, mul_one, pow_two]
    rw [hkcard, hk2, hdiff] at hpdiv
    rcases hp.dvd_mul.mp hpdiv with hpq | hpq
    · exact hpne ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow hpq))
    · exact hp.not_dvd_one (by simpa only [hcop.symm] using Nat.dvd_gcd (dvd_refl p) hpq)
  rw [hkcard]
  exact Nat.pow_le_pow_right (by positivity) (by omega)

/-- The point two-core is the literal complement required at the end of 15.3. -/
public theorem Context.point_twoCore_complement_of_involutions
    (hinv : ∀ v ∈ V, PFAppendixIII.IsInvolution v → v ∈ A) (hlt : A < V)
    (hnot : ¬ IsPGroup 2 J) :
    ((D).subgroupOf M).IsComplement' (pCore 2 M) := by
  have hdis := d.point_twoCore_disjoint_pair_of_involutions hinv
  have hVM : V ≤ M := map_subtype_le _
  have hDV : D ≤ normalizer (V : Set G) := by
    have hMV : M ≤ normalizer (V : Set G) := by
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
        (pCore 2 M).le_normalizer_map M.subtype
    exact inf_le_left.trans hMV
  have hprod := card_sup_eq_mul_of_normalizes_of_disjoint V D hDV hdis
  have hbound := card_le_of_le (sup_le hVM (show D ≤ M from inf_le_left))
  rw [hprod] at hbound
  have hM := linear_stabilizer_card_of_degree d.action d.t_not_mem_M d.degree_and_fixed.1
  have hVlower := d.point_twoCore_card_lower_of_involutions hinv hlt hnot
  have hcard : Nat.card V * Nat.card D = Nat.card M := by
    apply le_antisymm hbound
    rw [hM]
    exact Nat.mul_le_mul_right _ hVlower
  apply isComplement'_of_card_mul_and_disjoint
  · rw [Nat.card_congr (subgroupOfEquivOfLe (show D ≤ M from inf_le_left)).toEquiv]
    rw [card_map_of_injective M.subtype_injective] at hcard
    exact (Nat.mul_comm _ _).trans hcard
  · apply disjoint_def.mpr
    intro v hvD hvV
    apply Subtype.ext
    exact disjoint_def.mp hdis (mem_map_of_mem M.subtype hvV) hvD

end BenderSuzuki.ZD.LinearExclusion
