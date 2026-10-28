module
public import Theory.SpecificGroups.PSL3.BinaryLocalRank
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank.Divisibility
public import Theory.SpecificGroups.PSL3.SplitPrimeRank
public import CFSG.Quasithin.ClassicalModels
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Theory.Quasithin.LocalRankEmbedding
/-!
# Binary degree-three component inspection from the full rank budget

For PSL₃(2ⁿ) with n>1, choose a prime divisor of 2ⁿ−1. The actual
projective Borel gives positive two-local rank at that prime. The full
diagonal torus gives ordinary rank at least two away from three; at
three the checked projective diagonal-and-cycle witness retains rank two
despite the cubic scalar kernel. Their sum contradicts the original
ordinary/local rank budget. The sole remaining endpoint is PSL₃(2),
transported through the actual PSL₂(7) equivalence.

Source: Aschbacher–Smith A.3.8, printed pp.45–46. This is the binary
linear-three row of the centerless nonnormal-component inspection.
-/

public section
open Matrix Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.QTComponents.BinaryThree
variable {S : Type*} [Group S] [Finite S]

/-- The full ordinary/local odd-prime budget reduces binary PSL₃ to its
field of order two, without assuming ordinary odd rank at most one. -/
theorem binary_exponent_eq_one
    (hr : ∀ p : ℕ, p.Prime → Odd p → twoLocalPrimeRank p S + primeRank p S ≤ 2)
    {n : ℕ} (hn : 1 ≤ n) (hmodel : ClassicalGroup.IsPSL S 3 (2^n)) : n = 1 := by
  obtain ⟨F,_,_,hc,⟨e⟩⟩ := hmodel
  by_contra hne
  have hgt : 1 < 2^n-1 := by
    have hh := Nat.pow_lt_pow_right (a:=2) (by decide) (by omega : 1<n)
    norm_num at hh
    omega
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : 2^n-1 ≠ 1)
  have hodd : Odd (2^n-1) := Nat.odd_iff.mpr (by
    have he := Nat.even_iff.mp (even_two.pow_of_ne_zero (by omega : n≠0))
    have hpos : 0 < 2^n := pow_pos (by decide) _
    omega)
  have hpo : Odd p := hodd.of_dvd_nat hd
  let : Fact p.Prime := ⟨hp⟩
  have hdF : p ∣ Nat.card F-1 := by simpa only [hc] using hd
  have hloc := PSL3.BinaryLocalRank.twoLocal_rank_pos F (by omega : 0<n) hc hdF
  have hord : 2 ≤ primeRank p PSL(3,F) := by
    by_cases hp3 : p=3
    · subst p
      exact Theory.SpecificGroups.SignedThreeCubicRank.linear_projective_of_three_dvd hdF
    · exact PSL3.SplitPrimeRank.projective_rank F hp3 hdF
  have hlocS : 1 ≤ twoLocalPrimeRank p S := hloc.trans
    (twoLocalPrimeRank_le_of_injective p e.symm.toMonoidHom e.symm.injective)
  have hordS : 2 ≤ primeRank p S := by
    rwa [← primeRank_equiv p e] at hord
  have hh := hr p hp hpo
  omega

/-- The retained binary PSL₃ endpoint carries the actual PSL₂(7) marking. -/
theorem binary_model_seven
    (hr : ∀ p : ℕ, p.Prime → Odd p → twoLocalPrimeRank p S + primeRank p S ≤ 2)
    {n : ℕ} (hn : 1 ≤ n) (hmodel : ClassicalGroup.IsPSL S 3 (2^n)) :
    ClassicalGroup.IsPSL S 2 7 := by
  have hn1 := binary_exponent_eq_one hr hn hmodel
  subst n
  obtain ⟨F,_,_,hc,⟨e⟩⟩ := hmodel
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod,pow_one] using hc)
  exact ⟨ZMod 7,inferInstance,inferInstance,by simp,
    ⟨(e.trans (Atlas.fieldEquivPSL 3 eF)).trans
      Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm⟩⟩
end CFSG.Quasithin.ChapterA.QTComponents.BinaryThree
