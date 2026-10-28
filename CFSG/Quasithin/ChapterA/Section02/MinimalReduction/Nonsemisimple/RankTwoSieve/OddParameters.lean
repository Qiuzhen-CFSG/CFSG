module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.SmallAliases
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.Symplectic
public import Theory.SpecificGroups.SL2.SmallOddComparisons
public import GorensteinWalter.Classification

/-!
# Odd field parameters in the source rank-two sieve

The concrete field in a classical model supplies its prime-power parameter.
For a nontrivial perfect source, an odd PSL₂ parameter is greater than three,
since the projective action over the three-element field is solvable.
This puts the completed family reductions into the literal A.2.12 alternatives.
-/
public section
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] {n q : ℕ}

private theorem odd_prime_power (hq : IsPrimePow q) (ho : Odd q) :
    GorensteinWalter.IsOddPrimePower q := by
  obtain ⟨r,e,hr,he,hq⟩ := (isPrimePow_nat_iff q).mp hq
  have hr2 : r ≠ 2 := by
    intro h
    have hqeven : Even q := by rw [← hq,h]; exact (even_two.pow_of_ne_zero (by omega))
    exact (Nat.not_even_iff_odd.mpr ho) hqeven
  exact ⟨r,e,hr,hr.odd_of_ne_two hr2,by omega,hq.symm⟩

/-- The field of an odd linear model supplies the literal source parameter. -/
theorem odd_psl_parameter (ho : Odd q) (hm : ClassicalGroup.IsPSL Q n q) :
    GorensteinWalter.IsOddPrimePower q := by
  obtain ⟨F,hF,hfin,hcard,_⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  apply odd_prime_power _ ho
  rw [← hcard,Nat.card_eq_fintype_card]
  exact FiniteField.isPrimePow_card F

/-- The square field of an odd unitary model supplies its fixed-field parameter. -/
theorem odd_psu_parameter (ho : Odd q) (hm : ClassicalGroup.IsPSU Q n q) :
    GorensteinWalter.IsOddPrimePower q := by
  obtain ⟨F,hF,hfin,J,hcard,_,_⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  apply odd_prime_power _ ho
  have hpp : IsPrimePow (q^2) := by
    rw [← hcard,Nat.card_eq_fintype_card]
    exact FiniteField.isPrimePow_card F
  exact (isPrimePow_pow_iff (by decide : (2:ℕ) ≠ 0)).mp hpp

/-- Perfectness excludes the odd three-element projective-line model. -/
theorem odd_psl_two_parameter_gt_three [Group.IsPerfect Q] (ho : Odd q)
    (hm : ClassicalGroup.IsPSL Q 2 q) : 3 < q := by
  have hpp := odd_psl_parameter ho hm
  obtain ⟨r,e,hr,_,he,hq⟩ := hpp
  have hle : r ≤ q := by
    rw [hq]
    exact Nat.le_self_pow (by omega) r
  have hq2 : 2 ≤ q := hr.two_le.trans hle
  by_contra hn
  have heq : q = 3 := by
    have hqne : q ≠ 2 := by
      intro h
      exact (by decide : ¬ Odd (2:ℕ)) (h ▸ ho)
    omega
  obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hm
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three (hcard.trans heq) inferInstance

variable [Finite Q] [Group.IsPerfect Q]
/-- Complete linear-family reduction, with precisely the source's odd parameters. -/
theorem linear_source_models (hr : primeRank 2 Q ≤ 2) {n q : ℕ}
    (hn : 2 ≤ n) (hq : n = 2 → 4 ≤ q) (hm : ClassicalGroup.IsPSL Q n q) :
    (∃ q, 3 < q ∧ GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL Q 2 q) ∨
      ∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL Q 3 q := by
  rcases linear_models_of_twoRank_le_two hr hn hq hm with ⟨q,ho,hm⟩ | ⟨q,ho,hm⟩
  · exact Or.inl ⟨q,odd_psl_two_parameter_gt_three ho hm,odd_psl_parameter ho hm,hm⟩
  · exact Or.inr ⟨q,odd_psl_parameter ho hm,hm⟩

/-- Complete symplectic-family reduction in the same literal source alternatives. -/
theorem symplectic_source_models (hr : primeRank 2 Q ≤ 2) {r q : ℕ}
    (hr0 : 1 ≤ r) (hq : r=1 → 4 ≤ q) (hm : ClassicalGroup.IsPSp Q r q) :
    (∃ q, 3 < q ∧ GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL Q 2 q) ∨
      ∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL Q 3 q := by
  rcases symplectic_models_of_twoRank_le_two hr hr0 hq hm with ⟨q,ho,hm⟩ | ⟨q,ho,hm⟩
  · exact Or.inl ⟨q,odd_psl_two_parameter_gt_three ho hm,odd_psl_parameter ho hm,hm⟩
  · exact Or.inr ⟨q,odd_psl_parameter ho hm,hm⟩
/-- The alternating branch, with its two projective-line aliases made explicit. -/
theorem alternating_source_models (hr : primeRank 2 Q ≤ 2) {n : ℕ}
    (hn : 5 ≤ n) (a : Q ≃* alternatingGroup (Fin n)) :
    (∃ q, 3 < q ∧ GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL Q 2 q) ∨
      Nonempty (Q ≃* alternatingGroup (Fin 7)) := by
  rcases alternating_models_of_twoRank_le_two hr hn a with ⟨q,ho,hm⟩ | hm
  · exact Or.inl ⟨q,odd_psl_two_parameter_gt_three ho hm,odd_psl_parameter ho hm,hm⟩
  · exact Or.inr hm

/-- All four small-derived constructors reduce to the source's odd alternatives. -/
theorem smallDerived_source_models (hr : primeRank 2 Q ≤ 2)
    (hm : KnownSimple.IsSmallDerivedCarrier Q) :
    (∃ q, 3 < q ∧ GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL Q 2 q) ∨
      ∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSU Q 3 q := by
  rcases smallDerived_models_of_twoRank_le_two hr hm with ⟨q,ho,hm⟩ | ⟨q,ho,hm⟩
  · exact Or.inl ⟨q,odd_psl_two_parameter_gt_three ho hm,odd_psl_parameter ho hm,hm⟩
  · exact Or.inr ⟨q,odd_psu_parameter ho hm,hm⟩

end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
open Subgroup
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- Exact odd parameters for the linear source quotient, from the original hypotheses. -/
theorem CounterexampleToTheoremA.centralQuotient_linear_source_models
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) {n q : ℕ} (hd : 2 ≤ n) (hq : n=2 → 4 ≤ q)
    (hm : ClassicalGroup.IsPSL (S ⧸ center S) n q) :
    (∃ q, 3 < q ∧ GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 2 q) ∨
      ∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 3 q := by
  let := h.2.2.2.1.isPerfect
  exact Nonsemisimple.RankTwoSieve.linear_source_models
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) hd hq hm
end CFSG.Quasithin.ChapterA.Section02
