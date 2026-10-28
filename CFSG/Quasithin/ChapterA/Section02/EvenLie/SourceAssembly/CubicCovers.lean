module

public import CFSG.Quasithin.ChapterA.Section02.OddCenterCovers
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.OffendingPrime
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.UnitaryRanks.EvenParameter

/-!
# The actual degree-three Case II exclusions in A.2.18

The center in the original counterexample is a nontrivial group for its
selected odd prime. The proved multiplier restriction bounds its order by
three. Thus its order and the selected prime are both three, and A.2.14
contradicts the actual projective degree-three rank bound. No rank-failure
implication remains an extra premise of this application.

The last theorem consumes an actual SU5 covering equivalence; its general
recognition from an arbitrary central quotient is a separate multiplier step.
Source: Aschbacher--Smith A.2.14 and A.2.18, printed pp.38 and 40.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] [IsQuasisimple G] {p : ℕ}

/-- The original source counterexample has odd center, without a prime-core premise. -/
theorem center_odd_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G) :
    Odd (Nat.card (center G)) := by
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  have ho := h.center_preimage_odd_card ih f hf
  rwa [h.center_preimage_eq_center ih f hf] at ho

private theorem rank_obstruction_of_center_three
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (h3 : Nat.card (center G) = 3) :
    2 < primeRank 3 (G ⧸ center G) := by
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  have hpd : p ∣ 3 := h3 ▸ h.prime_dvd_center ih
  have hp3 : p = 3 := ((Nat.dvd_prime Nat.prime_three).mp hpd).resolve_left
    h.2.2.2.2.1.ne_one
  subst p
  exact lemma_A_2_14_center h ih h3

/-- Every binary PSL3 central quotient is excluded in the original Case II. -/
theorem caseII_linear_three_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {a : ℕ} (ha : 0 < a)
    (iso : ClassicalGroup.IsPSL (G ⧸ center G) 3 (2 ^ a)) : False := by
  exact h.center_ne_bot ih (OddCenterCovers.binary_linear_center_eq_bot_of_a214 ha iso
    (center_odd_of_source h ih) (rank_obstruction_of_center_three h ih))

/-- Every binary PSU3 central quotient in its simple parameter range is excluded in Case II. -/
theorem caseII_unitary_three_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {a : ℕ} (ha : 2 ≤ a)
    (iso : ClassicalGroup.IsPSU (G ⧸ center G) 3 (2 ^ a)) : False := by
  exact h.center_ne_bot ih (OddCenterCovers.unitary_center_eq_bot_of_a214 ha iso
    (center_odd_of_source h ih) (rank_obstruction_of_center_three h ih))

omit [IsQuasisimple G] in
/-- Once the literal special-unitary cover is recognized, the original counterexample is impossible. -/
theorem caseII_special_unitary_five
    (h : CounterexampleToTheoremA K G S p) {a : ℕ} (ha : 0 < a)
    (iso : IsSpecialUnitaryModel G 5 (2 ^ a)) : False := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := iso
  exact unitary_five_cover_not_quasithin J hcard
    (even_two.pow_of_ne_zero (by omega))
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) ha) hconj e h.1

/-- Compatibility wrapper retaining the explicit prime-primary center. -/
theorem caseII_linear_three
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hP : IsPGroup p (center G)) {a : ℕ} (ha : 0 < a)
    (iso : ClassicalGroup.IsPSL (G ⧸ center G) 3 (2 ^ a)) : False := by
  have _primary := hP
  exact caseII_linear_three_of_source h ih ha iso

/-- Compatibility wrapper retaining the explicit prime-primary center. -/
theorem caseII_unitary_three
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hP : IsPGroup p (center G)) {a : ℕ} (ha : 2 ≤ a)
    (iso : ClassicalGroup.IsPSU (G ⧸ center G) 3 (2 ^ a)) : False := by
  have _primary := hP
  exact caseII_unitary_three_of_source h ih ha iso

end CFSG.Quasithin.ChapterA.Section02.EvenLie
