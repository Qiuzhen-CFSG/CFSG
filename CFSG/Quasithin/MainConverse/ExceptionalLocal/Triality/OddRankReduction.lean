module

public import CFSG.Quasithin.Defs
public import Theory.SpecificGroups.Triality.ParabolicLocalStructure
public import Theory.SpecificGroups.Triality.FullParabolicActions.CyclicQuotient
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear

/-!
# Odd rank from the genuine triality local quotients

The full parabolic is larger than its local factor `O^{2'}`. Its odd-prime
rank is at most two once a cyclic character has precisely that local factor
as kernel and the local factor modulo its intrinsic two-core is identified
with characteristic-two PSL₂. The two-core contributes no odd rank, the
rank-one quotient contributes at most one, and the cyclic image contributes
at most one.

The final theorem discharges both concrete inputs using the proved Levi
identifications and the torus quotient calculation, including q = 2.
Coverage of arbitrary maximal two-locals is supplied in the parent module.
The source application is Aschbacher–Smith, Theorem 0.1.2(1), printed pp.3–4 and 481–482;
the local factors are those of F.1.12(I)(4), printed pp.263–264. The torus
extension is part of GLS3 2.6.5, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

namespace CFSG.Quasithin.MainConverse.TrialityLocal

open Subgroup Triality.Standard Triality.Standard.Parabolics
open scoped MatrixGroups

private theorem odd_primeRank_twoGroup {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p G = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
  intro hd
  obtain ⟨n, hn⟩ := hG.exists_card_eq
  rw [hn] at hd
  have hp2 : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
  exact ho.not_two_dvd_nat (by simp only [hp2, dvd_refl])

private theorem psl2_odd_primeRank_le_one (F : Type*) [Field F] [Finite F]
    [CharP F 2] {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p PSL(2, F) ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  rw [← Theory.GroupTheory.primeRank_equiv p (Theory.PSL2.sl2QuotientEquiv F)]
  let S : Sylow p SL(2, F) := default
  apply S.primeRank_le_one_of_isCyclic
  exact Matrix.SL2.odd_pGroup_isCyclic_of_injective S.isPGroup'
    (by rintro rfl; exact ho.not_two_dvd_nat (dvd_refl 2))
    (S : Subgroup SL(2, F)).subtype (S : Subgroup SL(2, F)).subtype_injective

/-- An actual PSL₂ identification of the local two-core quotient bounds
every odd-prime rank of the local factor by one, including at q = 2. -/
theorem localFactor_primeRank_le_one_of_quotient (P : Parameters) (a : Node)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (e : (localFactor P a ⧸ pCore 2 (localFactor P a)) ≃* PSL(2, F))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p (localFactor P a) ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have h := Theory.GroupTheory.primeRank_le_ker_add
    (p := p) (QuotientGroup.mk' (pCore 2 (localFactor P a)))
  rw [QuotientGroup.ker_mk', odd_primeRank_twoGroup pCore_isPGroup hp ho,
    zero_add, Theory.GroupTheory.primeRank_equiv p e] at h
  exact h.trans (psl2_odd_primeRank_le_one F hp ho)

/-- The cyclic quotient of the full parabolic contributes at most one
additional odd generator. Its kernel must be the actual embedded local
factor, not an arbitrary rank-one subgroup. -/
theorem parabolic_primeRank_le_two_of_quotient_character (P : Parameters) (a : Node)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (e : (localFactor P a ⧸ pCore 2 (localFactor P a)) ≃* PSL(2, F))
    {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (χ : parabolic P a →* C)
    (hχ : χ.ker = (localFactor P a).subgroupOf (parabolic P a))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p (parabolic P a) ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hker : primeRank p χ.ker ≤ 1 := by
    rw [hχ, Theory.GroupTheory.primeRank_equiv p
      (subgroupOfEquivOfLe (localFactor_le_parabolic P a))]
    exact localFactor_primeRank_le_one_of_quotient P a F e hp ho
  have hC : primeRank p C ≤ 1 := by
    let S : Sylow p C := default
    exact S.primeRank_le_one_of_isCyclic inferInstance
  exact (Theory.GroupTheory.primeRank_le_ker_add χ).trans
    (show primeRank p χ.ker + primeRank p C ≤ 2 from Nat.add_le_add hker hC)

/-- Equivalently it suffices to prove that the intrinsic quotient by the
embedded local factor is cyclic. Relative normality is already established
for the genuine parabolic candidates. -/
theorem parabolic_primeRank_le_two_of_cyclic_quotient (P : Parameters) (a : Node)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (e : (localFactor P a ⧸ pCore 2 (localFactor P a)) ≃* PSL(2, F))
    (hcyc : IsCyclic (parabolic P a ⧸
      (localFactor P a).subgroupOf (parabolic P a)))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p (parabolic P a) ≤ 2 := by
  let := hcyc
  exact parabolic_primeRank_le_two_of_quotient_character P a F e
    (QuotientGroup.mk' ((localFactor P a).subgroupOf (parabolic P a)))
    (QuotientGroup.ker_mk' _) hp ho

/-- Every odd-prime rank of either genuine full parabolic is at most two.
The actual PSL₂ quotient and cyclic torus quotient discharge all local inputs,
also for the central Levi PSL₂(2), without assuming perfectness. -/
theorem parabolic_primeRank_le_two (P : Parameters) (hp : P.prime = 2) (a : Node)
    {p : ℕ} (hprime : p.Prime) (hodd : Odd p) :
    primeRank p (parabolic P a) ≤ 2 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  let : CharP (GaloisField P.prime P.exponent) 2 :=
    hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
  cases a with
  | arms =>
    exact parabolic_primeRank_le_two_of_cyclic_quotient P .arms
      (ExtensionField P) (localFactorArmsQuotientEquivPSL2 P hp)
      (parabolic_quotient_isCyclic P hp .arms) hprime hodd
  | central =>
    exact parabolic_primeRank_le_two_of_cyclic_quotient P .central
      (GaloisField P.prime P.exponent) (localFactorCentralQuotientEquivPSL2 P hp)
      (parabolic_quotient_isCyclic P hp .central) hprime hodd

end CFSG.Quasithin.MainConverse.TrialityLocal
