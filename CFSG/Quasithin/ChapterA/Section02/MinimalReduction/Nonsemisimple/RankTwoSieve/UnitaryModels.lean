module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.OddParameters
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.UnitaryHigher
public import Theory.SpecificGroups.ClassicalUnitary.OddRankOneComparison

/-!
# The complete unitary family in the source alternatives

The actual degree-two unitary group is PSL₂ over its stored fixed field,
in either characteristic. The higher-dimensional bound leaves degree three;
its binary root-rank bound leaves PSU₃(4), while odd fields are retained.
This discharges the full unitary catalogue branch of A.2.12, printed p.36.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q]

theorem unitary_two_linear {q : ℕ} (hq : IsPrimePow q)
    (hm : ClassicalGroup.IsPSU Q 2 q) : ClassicalGroup.IsPSL Q 2 q := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨a⟩⟩ := hm
  have hk := J.fixed_card_prime_power hq hcard hconj
  refine ⟨FixedBy.subfield F J.conj,inferInstance,inferInstance,hk,?_⟩
  by_cases ho : Odd q
  · obtain ⟨b⟩ := J.nonempty_projectiveTwoEquiv_odd hq ho hcard hconj
    exact ⟨a.trans b⟩
  · obtain ⟨p,e,hp,he,hpe⟩ := (isPrimePow_nat_iff q).mp hq
    have hp2 : p=2 := by
      by_contra hp2
      exact ho (hpe ▸ (hp.odd_of_ne_two hp2).pow)
    subst p
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (f:=e*2) (by
      rw [← Nat.card_eq_fintype_card,hcard,← hpe,pow_mul])
    obtain ⟨b⟩ := Theory.SpecificGroups.UnitaryRootNormalizer.nonempty_projectiveTwoEquiv
      J hcard hk
    exact ⟨a.trans b⟩

variable [Finite Q] [Group.IsPerfect Q]
theorem unitary_source_models (hr : primeRank 2 Q ≤ 2) {d q : ℕ}
    (hp : KnownSimple.UnitaryParameters d q) (hm : ClassicalGroup.IsPSU Q d q) :
    ((∃ q, 3 < q ∧ GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL Q 2 q) ∨
      ∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL Q 3 q) ∨
    (∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSU Q 3 q) ∨
      ClassicalGroup.IsPSU Q 3 4 := by
  have hd := unitary_degree_le_three hr hp hm
  have he : d=2 ∨ d=3 := by have := hp.2.1; omega
  rcases he with rfl | rfl
  · exact Or.inl (linear_source_models hr (by decide) (fun _ => hp.2.2.1 rfl)
      (unitary_two_linear hp.1 hm))
  · by_cases ho : Odd q
    · exact Or.inr (Or.inl ⟨q,odd_psu_parameter ho hm,hm⟩)
    · obtain ⟨p,e,hp0,he,hpe⟩ := (isPrimePow_nat_iff q).mp hp.1
      have hp2 : p=2 := by
        by_contra hp2
        exact ho (hpe ▸ (hp0.odd_of_ne_two hp2).pow)
      subst p
      subst q
      exact Or.inr (Or.inr (psu_three_four_of_binary_model hr he (hp.2.2.2 rfl) hm))
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}
/-- Inspect every unitary model on the literal original source quotient. -/
theorem CounterexampleToTheoremA.centralQuotient_unitary_source_models
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) {d q : ℕ} (hp : KnownSimple.UnitaryParameters d q)
    (hm : ClassicalGroup.IsPSU (S ⧸ center S) d q) :
    ((∃ q, 3 < q ∧ GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 2 q) ∨
      ∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 3 q) ∨
    (∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSU (S ⧸ center S) 3 q) ∨
      ClassicalGroup.IsPSU (S ⧸ center S) 3 4 := by
  let := h.2.2.2.1.isPerfect
  exact Nonsemisimple.RankTwoSieve.unitary_source_models
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) hp hm
end CFSG.Quasithin.ChapterA.Section02
