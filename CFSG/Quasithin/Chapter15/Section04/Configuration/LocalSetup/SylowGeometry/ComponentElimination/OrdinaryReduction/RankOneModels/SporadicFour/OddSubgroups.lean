module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.Orders
public import GorensteinWalter.PSL2CoprimeSylowCyclic
public import BenderSuzuki.External.Huppert.II.theorem_8_27

/-!
# Odd subgroups of the ordinary rank-one models

For field order a power of two or an odd prime, every odd prime-power
subgroup of PSL₂ is cyclic. Away from the characteristic this is the
coprime-field Sylow theorem. At an odd defining prime, the additive-field
Sylow subgroup has prime order. For q < 7 the order formula excludes every
odd prime square from the group order, so its odd prime-power subgroups
have order at most their defining prime.

This is the structural comparison used to eliminate four fixed sporadic
carriers from the ordinary branch of 15.4.20. No sporadic order or
simplicity hypothesis occurs here.

Source: Aschbacher–Smith, full 1.1.5(3)(f), printed pp.501–503, and the
proof of 15.4.20, printed p.1164; the imported matrix results formalize
Huppert II.8.2 and II.8.5.
-/

@[expose] public section
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels

private theorem small_parameter_cyclic {G : Type*} [Group G] [Finite G]
    {r q : ℕ} [Fact r.Prime] (hr : r ≠ 2) (P : Subgroup G)
    (hP : IsPGroup r P) (hm : ClassicalGroup.IsPSL G 2 q) (hq : q < 7) :
    IsCyclic P := by
  by_contra hcyc
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk1 : k ≤ 1 := by omega
    exact hcyc (isCyclic_of_card_dvd_prime (p := r) (by
      rw [hk]
      simpa using pow_dvd_pow r hk1))
  have hdiv : r^2 ∣ Nat.card G := by
    exact dvd_trans (hk ▸ pow_dvd_pow r hk2) (Subgroup.card_subgroup_dvd_card P)
  have hnum : r^2 ∣ q * (q^2-1) := by
    rw [← psl_two_card_mul hm]
    exact dvd_mul_of_dvd_left hdiv _
  have hq2 : 2 ≤ q := by
    obtain ⟨F, _, _, hF, _⟩ := hm
    have := Finite.one_lt_card (α := F)
    omega
  have hbound : q * (q^2-1) ≤ 210 := by
    calc
      _ ≤ 6 * (6^2-1) := Nat.mul_le_mul (by omega)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1)
      _ = _ := by norm_num
  have hpos : 0 < q * (q^2-1) := by
    have : 1 < q^2 := by nlinarith
    exact Nat.mul_pos (by omega) (by omega)
  have hrbound := (Nat.le_of_dvd hpos hnum).trans hbound
  have hr14 : r ≤ 14 := by nlinarith
  have hrprime : r.Prime := Fact.out
  interval_cases r <;> norm_num at hrprime
  all_goals try omega
  all_goals interval_cases q <;> try norm_num at hnum

/-- The odd prime-power subgroups of an ordinary rank-one model are cyclic. -/
theorem ordinary_rank_one_odd_subgroup_cyclic {G : Type*} [Group G] [Finite G]
    {r q : ℕ} [Fact r.Prime] (hr : r ≠ 2) (P : Subgroup G)
    (hP : IsPGroup r P)
    (hq : (∃ n : ℕ, Even n ∧ q = 2^n) ∨ q.Prime ∧ Odd q)
    (hm : ClassicalGroup.IsPSL G 2 q) : IsCyclic P := by
  by_cases hsmall : q < 7
  · exact small_parameter_cyclic hr P hP hm hsmall
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨R, hR⟩ := (hP.map e.toMonoidHom).exists_le_sylow
  have hRcyc : IsCyclic R := by
    rcases hq with ⟨n, _, rfl⟩ | ⟨hqprime, _⟩
    · let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      apply GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F hF
        (by omega) r hr
      rw [hF]
      exact (Nat.coprime_primes (Fact.out : r.Prime) Nat.prime_two).mpr hr |>.pow_right n
    · let : Fact q.Prime := ⟨hqprime⟩
      by_cases hrq : r = q
      · subst r
        obtain ⟨a⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive
          (F := F) (p := q) (f := 1) (by simpa using hF) R
        apply isCyclic_of_prime_card (p := q)
        exact (Nat.card_congr a.toEquiv).symm.trans hF
      · apply GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F
          (p := q) (f := 1) (by simpa using hF) (by omega) r hr
        rw [hF]
        exact (Nat.coprime_primes (Fact.out : r.Prime) hqprime).mpr hrq
  let := hRcyc
  have hmap : IsCyclic (P.map e.toMonoidHom) := Subgroup.isCyclic_of_le hR
  exact (MulEquiv.subgroupMap e P).isCyclic.mpr hmap

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
