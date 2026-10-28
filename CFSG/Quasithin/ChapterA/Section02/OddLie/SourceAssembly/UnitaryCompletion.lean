module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.UnitaryTernary
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.LocalThreePart
public import Theory.SpecificGroups.ClassicalUnitary.HigherUnitaryTernary
public import Theory.Quasithin.CentralElementaryTernaryQuotient

/-!
# Completion of the odd unitary source Case II

Every model reduces to fixed field three and degree at least four. In
degree four, the elementary center has order dividing nine and every
actual model two-local has three-part at most nine. The finite local
quotient-rank theorem proves quasithinness of the original offending
partial-center quotient. Together with ordinary rank at least three, this
discharges both clauses of Theorem A and contradicts its failure witness.

In higher degree, the four-space elementary 3⁴ subgroup centralizes an
actual involution, so lifting through the odd center contradicts QT directly.
No general descent of quasithinness through odd kernels is asserted.
Source: Aschbacher–Smith A.2.17 and I.2.1, printed pp.39 and 409.
-/

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
universe u
variable {K : GroupClass.{u}} {G S : Type u} [Group G] [Finite G] [Group S] [Finite S]
  [IsQuasisimple G] {p : ℕ}

public theorem unitary_four_three_caseII
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hP : IsPGroup p (center G))
    (model : ClassicalGroup.IsPSU (G ⧸ center G) 4 3) : False := by
  obtain ⟨hp3,hZE,hZcard,hrank⟩ := unitary_four_ternary_source_inputs h ih hP model
  subst p
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨iso⟩⟩ := model
  obtain ⟨e⟩ := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.exists_model_equiv
    J (by simpa using hcard) hconj
  let q := (iso.trans e).toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hq : q.ker = center G := by
    rw [MonoidHom.ker_comp_of_injective _ _ (iso.trans e).injective,QuotientGroup.ker_mk']
  let : IsElementaryAbelian 3 q.ker := hq.symm ▸ hZE
  obtain ⟨N,hN,_,hNC,⟨es⟩⟩ := h.quotient_by_nontrivial_center_subgroup ih.theoremA
  let := hN
  have hQT : IsQuasithin (G ⧸ N) :=
    Theory.Quasithin.CentralElementaryTernaryQuotient.isQuasithin_quotient q hq.le
      (hq.symm ▸ hZcard)
      Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.twoLocal_three_part
      N (hNC.trans hq.ge) h.1
  have huq := isQuasithin_iff_twoLocalPrimeRank.mp hQT 3 (by decide) (by decide)
  have hug := isQuasithin_iff_twoLocalPrimeRank.mp h.1 3 (by decide) (by decide)
  have hc : TheoremAConclusion G (G ⧸ N) 3 :=
    ⟨.inl ⟨lemma_A_2_7_4 N (by decide) huq,hug⟩,fun hl => (by omega)⟩
  exact h.2.2.2.2.2.2 (hc.of_mulEquiv es.symm)

public theorem unitary_caseII
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hP : IsPGroup p (center G)) {n r e : ℕ} [Fact r.Prime]
    (hn : 2 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSU (G ⧸ center G) n (r^e)) : False := by
  obtain ⟨hn4,rfl,rfl⟩ := unitary_caseII_parameters h ih hP hn hr he model
  simp only [pow_one] at model
  by_cases hn : n = 4
  · subst n
    exact unitary_four_three_caseII h ih hP model
  obtain ⟨k,hk,rfl⟩ : ∃ k, 0 < k ∧ n = 4+k := ⟨n-4,by omega,by omega⟩
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨iso⟩⟩ := model
  have ho : Odd (Nat.card (center G)) := by
    let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
    obtain ⟨k,hk⟩ := hP.exists_card_eq
    rw [hk]
    exact h.2.2.2.2.2.1.pow
  exact Theory.SpecificGroups.ClassicalUnitary.HigherUnitaryTernary.not_quasithin_of_odd_center_quotient
    hk J (by simpa using hcard) hconj iso ho h.1
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
