module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.CubicCovers
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime.Source
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient

/-!
# The full unitary-four Case II source branch

The literal PSU4 model is identified with the antidiagonal SU4 model through
its original Hermitian form. Its actual perfect central covering has no odd
kernel prime by the completed torus and point-index calculation. The selected
prime divides the nontrivial center of the original counterexample, giving
the source contradiction for every positive binary field exponent, including
q=2. No projective simplicity or multiplier recognition premise is added.
Source: Aschbacher--Smith A.2.18, printed p.40.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] [IsQuasisimple G] {p : ℕ}

/-- The full binary PSU4 central-quotient branch is impossible in the actual Case II. -/
theorem caseII_unitary_four_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {a : ℕ} (ha : 0 < a)
    (iso : ClassicalGroup.IsPSU (G ⧸ center G) 4 (2 ^ a)) : False := by
  obtain ⟨F, hF, hfin, J, hc, hconj, ⟨e⟩⟩ := iso
  obtain ⟨ep⟩ := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport.nonempty_projectiveEquiv_standardSU
    J a ha hc hconj
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  have hp2 : p ≠ 2 := by
    intro he
    have ho := h.2.2.2.2.2.1
    rw [he] at ho
    exact (by decide : ¬ Odd (2 : ℕ)) ho
  have hd : p ∣ Nat.card (center G) := h.prime_dvd_center ih
  have hn := Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime.not_dvd_kernel_binary
    J a ha hc hconj hp2 (centralQuotientCover (e.trans ep))
  exact hn (by rwa [centralQuotientCover_ker])

/-- Compatibility wrapper retaining the explicit prime-primary center. -/
theorem caseII_unitary_four
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hP : IsPGroup p (center G)) {a : ℕ} (ha : 0 < a)
    (iso : ClassicalGroup.IsPSU (G ⧸ center G) 4 (2 ^ a)) : False := by
  have _primary := hP
  exact caseII_unitary_four_of_source h ih ha iso

end CFSG.Quasithin.ChapterA.Section02.EvenLie
