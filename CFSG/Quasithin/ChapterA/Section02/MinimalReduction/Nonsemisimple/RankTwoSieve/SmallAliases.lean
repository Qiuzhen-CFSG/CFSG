module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.SmallFamilies
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.Ree
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.TitsReeF4
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SU3.BinaryG2Comparison

/-!
# Alternating and small-derived entries in source normal form

The elementary-eight obstruction reduces the alternating family to A₅,A₆,A₇.
The actual exceptional isomorphisms replace the first two by PSL₂(5),PSL₂(9).
Of the four separate small-derived catalogue entries, the binary symplectic
one is A₆ and binary G₂ is PSU₃(3); small Ree and Tits have already been
excluded by their concrete rank-three witnesses. Thus these entire catalogue
families reduce to the literal alternatives of A.2.12.
Source: Aschbacher–Smith A.2.12, printed p.36; exceptional comparisons cited
in the imported model modules.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q]

private theorem five_of_alternating (a : Q ≃* alternatingGroup (Fin 5)) :
    ClassicalGroup.IsPSL Q 2 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨b⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  exact ⟨ZMod 5,inferInstance,inferInstance,by simp,⟨a.trans b.symm⟩⟩

private theorem nine_of_alternating (a : Q ≃* alternatingGroup (Fin 6)) :
    ClassicalGroup.IsPSL Q 2 9 := by
  exact ⟨GaloisField 3 2,inferInstance,inferInstance,
    by simpa using GaloisField.card 3 2 (by decide),
    ⟨a.trans Atlas.Comparisons.Exceptional.psl2NineEquivAlt6.symm⟩⟩

private theorem ternary_unitary_of_binary_g2
    (a : Q ≃* commutator (Atlas.G2.Model (ZMod 2))) : ClassicalGroup.IsPSU Q 3 3 := by
  obtain ⟨b⟩ := Atlas.G2.nonempty_commutator_binary_equiv_psu3
  refine ⟨GaloisField 3 2,inferInstance,inferInstance,ABG.unitaryForm 3 3 1 (by decide),
    GaloisField.card 3 2 (by decide),?_,⟨a.trans b⟩⟩
  intro x
  change iterateFrobeniusEquiv (GaloisField 3 2) 3 1 x = x ^ 3
  simp only [iterateFrobeniusEquiv_def,pow_one]

variable [Finite Q]

/-- The complete simple-range alternating family reduces to odd PSL₂ or A₇. -/
theorem alternating_models_of_twoRank_le_two (hr : primeRank 2 Q ≤ 2) {n : ℕ}
    (hn : 5 ≤ n) (a : Q ≃* alternatingGroup (Fin n)) :
    (∃ q : ℕ, Odd q ∧ ClassicalGroup.IsPSL Q 2 q) ∨
      Nonempty (Q ≃* alternatingGroup (Fin 7)) := by
  have hle := alternating_degree_le_seven hr a
  have hcases : n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact Or.inl ⟨5,by decide,five_of_alternating a⟩
  · exact Or.inl ⟨9,by decide,nine_of_alternating a⟩
  · exact Or.inr ⟨a⟩

/-- All four literal small-derived catalogue constructors are discharged. -/
theorem smallDerived_models_of_twoRank_le_two (hr : primeRank 2 Q ≤ 2)
    (hmodel : KnownSimple.IsSmallDerivedCarrier Q) :
    (∃ q : ℕ, Odd q ∧ ClassicalGroup.IsPSL Q 2 q) ∨
      ∃ q : ℕ, Odd q ∧ ClassicalGroup.IsPSU Q 3 q := by
  cases hmodel with
  | symplectic iso =>
    obtain ⟨a⟩ := iso
    exact Or.inl ⟨9,by decide,nine_of_alternating
      (a.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)⟩
  | g2 iso =>
    obtain ⟨a⟩ := iso
    exact Or.inr ⟨3,by decide,ternary_unitary_of_binary_g2 a⟩
  | ree iso => exact (no_smallRee_model hr iso.some).elim
  | tits iso => exact (no_tits_model hr iso.some).elim

end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- Full alternating-family inspection for the literal source quotient. -/
theorem CounterexampleToTheoremA.centralQuotient_alternating_models
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hns : ¬ IsSemisimple G) {n : ℕ} (hn : 5 ≤ n)
    (a : (S ⧸ center S) ≃* alternatingGroup (Fin n)) :
    (∃ q : ℕ, Odd q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 2 q) ∨
      Nonempty ((S ⧸ center S) ≃* alternatingGroup (Fin 7)) :=
  Nonsemisimple.RankTwoSieve.alternating_models_of_twoRank_le_two
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hns) hn a

/-- All four small-derived branches for the literal source quotient. -/
theorem CounterexampleToTheoremA.centralQuotient_smallDerived_models
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hns : ¬ IsSemisimple G) (hmodel : KnownSimple.IsSmallDerivedCarrier (S ⧸ center S)) :
    (∃ q : ℕ, Odd q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 2 q) ∨
      ∃ q : ℕ, Odd q ∧ ClassicalGroup.IsPSU (S ⧸ center S) 3 q :=
  Nonsemisimple.RankTwoSieve.smallDerived_models_of_twoRank_le_two
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hns) hmodel

end CFSG.Quasithin.ChapterA.Section02
