module
public import Theory.SpecificGroups.Classical.ThreeCoverLocalRanks
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
/-! # Odd-prime rank in the binary rank-two models
For PSL₃(2ⁿ), n>1, a prime divisor of 2ⁿ−1 gives the two split torus
directions. The scalar prime three is handled by the genuine projective
diagonal/cycle witness. For PSp₄ the embedded binary derived subgroup
already has cubic rank two. These actual model ranks force normality of
components in the source SQTK ambient group, including central two-covers.
Source: Aschbacher--Smith 1.2.1(3) used in 2.5.7, printed p.554. -/
public section
open Subgroup Theory.GroupTheory
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.BorelQuotient
open scoped MatrixGroups
namespace Theory.SpecificGroups.Classical.EvenRankTwoOddRank
variable {F : Type*} [Field F] [Finite F]
theorem linear {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n) :
    ∃ p:ℕ, p.Prime ∧ Odd p ∧ 2≤primeRank p PSL(3,F) := by
  have hq : 2<2^n := by
    calc 2=2^1 := by norm_num
         _ < 2^n := Nat.pow_lt_pow_right (by decide) hn
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (show 2^n-1≠1 by omega)
  let : Fact p.Prime := ⟨hp⟩
  have ho : Odd p := hp.odd_of_ne_two (by
    intro he
    subst p
    obtain ⟨a,ha⟩ := Even.pow_of_ne_zero (by decide : Even (2:ℕ)) (show n≠0 by omega)
    obtain ⟨b,hb⟩ := hd
    omega)
  refine ⟨p,hp,ho,?_⟩
  by_cases h3 : p=3
  · subst p
    exact Theory.SpecificGroups.SignedThreeCubicRank.linear_projective hF
      ((Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mp hd)
  have hcop3 : Nat.Coprime p 3 := hp.coprime_iff_not_dvd.mpr (fun hh =>
    h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hh))
  have hker : Nat.Coprime p (Nat.card (Matrix.PSL3.projection F).ker) := by
    apply hcop3.of_dvd_right
    rw [Matrix.PSL3.card_projectionKernel]
    exact Nat.gcd_dvd_left _ _
  rw [← primeRank_eq_of_surjective_of_coprime p (Matrix.PSL3.projection F)
    (Matrix.PSL3.projection_surjective F) hker]
  have hr : 1≤primeRank p Fˣ := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro he
    apply PrimeRank.eq_zero_iff_not_dvd_card.mp he
    rwa [Nat.card_units,hF]
  have hprod : 2≤primeRank p (Fˣ×Fˣ) := by
    rw [primeRank_prod_eq_add]
    omega
  exact hprod.trans (Theory.GroupTheory.primeRank_le_of_injective p (torusSL F) (torusSL_injective F))

theorem symplectic [CharP F 2] : 2≤primeRank 3 (Matrix.symplecticGroup (Fin 2) F ⧸ center (Matrix.symplecticGroup (Fin 2) F)) := by
  have h := Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic (F:=F)
  have hs := h.trans (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Matrix.symplecticGroup (Fin 2) F)).subtype
    (commutator _).subtype_injective)
  rwa [primeRank_equiv 3 Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv] at hs
end Theory.SpecificGroups.Classical.EvenRankTwoOddRank
