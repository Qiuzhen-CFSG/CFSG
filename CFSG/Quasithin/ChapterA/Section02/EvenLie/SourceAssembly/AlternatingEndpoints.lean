module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.CubicCovers

/-!
# The alternating endpoints in the even-Lie source dispatch

The original counterexample already supplies odd center and divisibility by
the offending prime. The actual alternating multiplier calculation forces
its nontrivial center to have order three, so the earlier A.2.14 obstruction
applies without an assumed prime-core identity. This covers the literal
PSL2(4) and PSp4(2)' endpoints through their proved alternating isomorphisms.
Source: Aschbacher--Smith A.2.16 and A.2.18, printed pp.38 and 40.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] [IsQuasisimple G] {p : ℕ}

/-- The source alternating-cover exclusion needs no prime-primary-center premise. -/
theorem caseII_alternating_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {n : ℕ} (hn : 5 ≤ n) (e : G ⧸ center G ≃* alternatingGroup (Fin n)) : False := by
  have hz1 : Nat.card (center G) ≠ 1 :=
    fun hc => h.center_ne_bot ih ((center G).eq_bot_of_card_eq hc)
  obtain ⟨_, hz⟩ := (GLS3.Chapter5.OddCentralCovers.odd_center_alternatives n hn e
    (center_odd_of_source h ih)).resolve_left hz1
  have h3 : IsPGroup 3 (center G) := IsPGroup.of_card (n := 1) (by simpa using hz)
  have hp3 := h.prime_eq_of_center_isPGroup ih h3
  subst p
  exact h.not_alternating_centralQuotient ih h3 hn e

end CFSG.Quasithin.ChapterA.Section02.EvenLie
