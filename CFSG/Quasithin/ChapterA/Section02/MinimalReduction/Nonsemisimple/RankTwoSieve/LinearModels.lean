module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.Linear
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.BinaryEndpoints
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters

/-!
# The split-linear rank-two catalogue branch in source normal form

Every admissible linear entry has degree two or three. In even characteristic,
the rank bounds leave PSL₂(4) and PSL₃(2); the actual exceptional isomorphisms
replace them by PSL₂(5) and PSL₂(7). Thus this entire catalogue family reduces
to the odd-field PSL₂ and PSL₃ alternatives appearing in A.2.12.
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q]

private theorem five_of_alt_five (a : Q ≃* alternatingGroup (Fin 5)) :
    ClassicalGroup.IsPSL Q 2 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨b⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  exact ⟨ZMod 5,inferInstance,inferInstance,by simp,⟨a.trans b.symm⟩⟩

private theorem five_of_binary_four (h : ClassicalGroup.IsPSL Q 2 4) :
    ClassicalGroup.IsPSL Q 2 5 := by
  obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := h
  obtain ⟨b⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hcard
  exact five_of_alt_five (a.trans b)

private theorem seven_of_linear_three_two (h : ClassicalGroup.IsPSL Q 3 2) :
    ClassicalGroup.IsPSL Q 2 7 := by
  obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let b : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact ⟨ZMod 7,inferInstance,inferInstance,by simp,
    ⟨(a.trans (Atlas.fieldEquivPSL 3 b)).trans
      Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm⟩⟩

private theorem odd_or_binary_parameter {n q : ℕ} (h : ClassicalGroup.IsPSL Q n q) :
    Odd q ∨ ∃ e : ℕ, 0 < e ∧ q = 2 ^ e := by
  obtain ⟨F,hF,hfin,hcard,_⟩ := h
  let : Fintype F := Fintype.ofFinite F
  have hp : IsPrimePow q := by
    rw [← hcard,Nat.card_eq_fintype_card]
    exact FiniteField.isPrimePow_card F
  obtain ⟨r,e,hr,he,hq⟩ := (isPrimePow_nat_iff q).mp hp
  by_cases h2 : r = 2
  · exact Or.inr ⟨e,he,by simpa only [h2] using hq.symm⟩
  · exact Or.inl (hq ▸ (hr.odd_of_ne_two h2).pow)

variable [Finite Q]

/-- The complete admissible linear catalogue branch, expressed in the source's
odd-field degree-two or degree-three alternatives. -/
theorem linear_models_of_twoRank_le_two (hr : primeRank 2 Q ≤ 2) {n q : ℕ}
    (hn : 2 ≤ n) (hq : n = 2 → 4 ≤ q) (hmodel : ClassicalGroup.IsPSL Q n q) :
    (∃ q : ℕ, Odd q ∧ ClassicalGroup.IsPSL Q 2 q) ∨
      ∃ q : ℕ, Odd q ∧ ClassicalGroup.IsPSL Q 3 q := by
  rcases linear_degree_two_or_three hr hn hmodel with rfl | rfl
  · rcases odd_or_binary_parameter hmodel with ho | ⟨e,he,rfl⟩
    · exact Or.inl ⟨q,ho,hmodel⟩
    have hle := psl_two_binary_exponent_le_two hr hmodel
    have hge := hq rfl
    have he2 : e = 2 := by
      have he1 : e ≠ 1 := by intro h; simp [h] at hge
      omega
    have hm : ClassicalGroup.IsPSL Q 2 4 := by
      simpa only [he2,show (2:ℕ)^2=4 from rfl] using hmodel
    exact Or.inl ⟨5,by decide,five_of_binary_four hm⟩
  · rcases odd_or_binary_parameter hmodel with ho | ⟨e,he,rfl⟩
    · exact Or.inr ⟨q,ho,hmodel⟩
    have he1 := psl_three_binary_exponent_eq_one hr he hmodel
    have hm : ClassicalGroup.IsPSL Q 3 2 := by simpa only [he1,pow_one] using hmodel
    exact Or.inl ⟨7,by decide,seven_of_linear_three_two hm⟩

end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- The full split-linear catalogue inspection on the literal source quotient. -/
theorem CounterexampleToTheoremA.centralQuotient_linear_models
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hns : ¬ IsSemisimple G) {n q : ℕ} (hn : 2 ≤ n) (hq : n = 2 → 4 ≤ q)
    (hmodel : ClassicalGroup.IsPSL (S ⧸ center S) n q) :
    (∃ q : ℕ, Odd q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 2 q) ∨
      ∃ q : ℕ, Odd q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 3 q :=
  Nonsemisimple.RankTwoSieve.linear_models_of_twoRank_le_two
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hns) hn hq hmodel

end CFSG.Quasithin.ChapterA.Section02
