module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ModelIntersection.Basic
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SU3.FixedFieldTwo
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import GorensteinWalter.PSL2CoprimeSylowCyclic

/-!
# Excluding the small models from the signed degree-three intersection

The alternating groups A₆ and A₇ and the linear group PSL₃(3) have orders
at most 5616. A signed degree-three model with the source congruence has
larger order: the linear parameter is at least four and the unitary parameter
is at least five, except for the solvable endpoint PSU₃(2). Quasisimplicity
excludes that endpoint. The comparison applies to the actual two-core
quotient, whose order divides the original group's order; it does not require
the two-core to vanish.

For PSL₂ over a prime field, the three-rank is at most one. Above field order
five the Sylow three-subgroups are cyclic by the coprime torus calculation.
The primes two, three and five are handled directly by their group orders
6, 12 and 60. Thus this branch contradicts the given three-rank two, even
without the Fermat--Mersenne restriction.

`small_models_excluded` supplies exactly the `hSmall` comparison required by
`ModelIntersection.intersection_of_carrier_comparisons`. All model witnesses
are actual multiplicative equivalences, and the unitary order calculation
retains the supplied Hermitian form and its fixed-field parameter.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.18(2),
printed pp.51--52; 1.1.5(3c--e), pp.501--503; and the intersections used on
pp.1135 and 1139. The carrier calculations are Huppert II.8.2--5 and II.10.12.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection
open Chapter1.Section02.LocalModels

private theorem prime_field_threeRank_le_one {F : Type*} [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) : primeRank 3 PSL(2,F) ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let P : Sylow 3 PSL(2,F) := default
  apply P.primeRank_le_one_of_isCyclic
  by_cases hlarge : 7 ≤ p
  · exact GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F
      (by simpa using hF : Nat.card F = p ^ 1) (hF ▸ hlarge) 3 (by decide)
      (by rw [hF]; exact (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)) P
  · have hcases : p = 2 ∨ p = 3 ∨ p = 5 := by
      interval_cases p <;> norm_num at hp <;> simp
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 2
    rw [hF] at hc
    rcases hcases with rfl | rfl | rfl
    all_goals
      norm_num [Fin.prod_univ_succ] at hc
      apply isCyclic_of_prime_card (p := 3)
      rw [P.card_eq_multiplicity]
    · have hcard : Nat.card PSL(2,F) = 6 := by omega
      rw [hcard]
      decide +kernel
    · have hcard : Nat.card PSL(2,F) = 12 := by omega
      rw [hcard]
      decide +kernel
    · have hcard : Nat.card PSL(2,F) = 60 := by omega
      rw [hcard]
      decide +kernel

private theorem linear_three_card_gt {S : Type*} [Group S] {q : ℕ}
    (hmodel : ClassicalGroup.IsPSL S 3 q) (hq : 4 ≤ q) : 5616 < Nat.card S := by
  obtain ⟨F, hfield, hfin, hc, ⟨e⟩⟩ := hmodel
  rw [Nat.card_congr e.toEquiv]
  have horder := Matrix.PSL3.LinearThree.card_projective_mul_scalar F
  rw [hc] at horder
  have hden : Nat.gcd 3 (q - 1) ≤ 3 := Nat.gcd_le_left _ (by decide)
  have hnum : 60480 ≤ q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) := by
    calc
      60480 = (4 : ℕ) ^ 3 * (4 ^ 3 - 1) * (4 ^ 2 - 1) := by norm_num
      _ ≤ q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) := by gcongr
  have hbound := Nat.mul_le_mul_left (Nat.card PSL(3,F)) hden
  rw [horder] at hbound
  omega

private theorem unitary_three_card_gt {S : Type*} [Group S] {q : ℕ}
    (hmodel : ClassicalGroup.IsPSU S 3 q) (hq : 5 ≤ q) : 5616 < Nat.card S := by
  have hpq := signed_parameter_primePower (unitary := true) hmodel
  obtain ⟨p, n, hp, hn, hpn⟩ := (isPrimePow_nat_iff q).mp hpq
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, hfield, hfin, J, hc, hconj, ⟨e⟩⟩ := hmodel
  have hfixed : Nat.card {x : F // J.conj x = x} = q := by
    rw [← hpn] at hc hconj ⊢
    exact FiniteField.card_fixed_of_quadratic_frobenius J.conj p n hn hc hconj
  rw [Nat.card_congr e.toEquiv, Representation.SU3.BinaryDegree.card_projective J hc hfixed]
  have hden : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left _ (by decide)
  have hnum : 378000 ≤ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
    calc
      378000 = ((5 : ℕ) ^ 3 + 1) * 5 ^ 3 * (5 ^ 2 - 1) := by norm_num
      _ ≤ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by gcongr
  apply Nat.lt_of_lt_of_le (by decide : 5616 < 5617)
  apply (Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_left _ (by decide))).mpr
  exact (Nat.mul_le_mul_left 5617 hden).trans (by omega)

private theorem signed_three_card_gt {S : Type*} [Group S] [IsQuasisimple S]
    {unitary : Bool} {q : ℕ} (hmod : q % 3 = (if unitary then 2 else 1))
    (hmodel : IsPSLSign S unitary 3 q) : 5616 < Nat.card S := by
  have hq := (signed_parameter_primePower hmodel).one_lt
  let : Nontrivial (S ⧸ center S) := IsQuasisimple.simple.toNontrivial
  let : Nontrivial S := (QuotientGroup.mk'_surjective (center S)).nontrivial
  cases unitary with
  | false => exact linear_three_card_gt hmodel (by change q % 3 = 1 at hmod; omega)
  | true =>
    by_cases htwo : q = 2
    · subst q
      obtain ⟨F, hfield, hfin, J, hc, hconj, ⟨e⟩⟩ := hmodel
      let := BenderSuzuki.MatrixGroups.HermitianForm.FixedFieldTwo.projective_isSolvable J hc hconj
      have hs : Group.IsSolvable S :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      exact (Group.IsPerfect.not_isSolvable S hs).elim
    · exact unitary_three_card_gt hmodel (by change q % 3 = 2 at hmod; omega)

private theorem small_card_le {S : Type*} [Group S]
    (hmodel : IsAlternating S 6 ∨ IsAlternating S 7 ∨ ClassicalGroup.IsPSL S 3 3) :
    Nat.card S ≤ 5616 := by
  rcases hmodel with h | h | ⟨F, hfield, hfin, hc, ⟨e⟩⟩
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  · rw [Nat.card_congr e.toEquiv, Matrix.PSL3.LinearThree.card_projective F, hc]
    norm_num

/-- The alternating and odd small-model alternatives cannot have the supplied
signed degree-three two-core quotient. This discharges the parent
intersection theorem's entire `hSmall` premise. -/
theorem small_models_excluded (S : Type*) [Group S] [Finite S] [IsQuasisimple S]
    (hodd : pPrimeCore 2 S = ⊥) (hrank : primeRank 3 S = 2)
    (hmodel : IsAlternating S 6 ∨ IsAlternating S 7 ∨ ClassicalGroup.IsPSL S 3 3 ∨
      ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL S 2 p)
    (unitary : Bool) (q : ℕ) (hmod : q % 3 = (if unitary then 2 else 1))
    (hsigned : IsPSLSign (S ⧸ pCore 2 S) unitary 3 q) : False := by
  have exclude_small (hsmall : Nat.card S ≤ 5616) : False := by
    let := twoCore_quotient_quasisimple hodd
    have hlarge := signed_three_card_gt hmod hsigned
    have hquot := Nat.le_of_dvd Nat.card_pos (pCore 2 S).card_quotient_dvd_card
    omega
  rcases hmodel with h | h | h | ⟨p, hp, F, hfield, hfin, hF, ⟨e⟩⟩
  · exact exclude_small (small_card_le (Or.inl h))
  · exact exclude_small (small_card_le (Or.inr (Or.inl h)))
  · exact exclude_small (small_card_le (Or.inr (Or.inr h)))
  · have hbound := prime_field_threeRank_le_one hp.1 hF
    rw [← primeRank_equiv 3 e, hrank] at hbound
    omega
end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection
