module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveExclusionsBinaryMovement
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveExclusionsJanko
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveExclusionsTernaryFive

/-!
# Applying the proved binary and parameter-five row exclusions

The literal secondary action excludes every binary PSL₂ quotient, and at
n = 2 excludes PSL₃(5) and J₁. Thus the only remaining nonexceptional row
is SU₃ or PSU₃. The second theorem applies these exclusions to the original
four-row proposition, preserving its exceptional outer-action clause.

The source alternatives remain an explicit, unproved premise here; these
lemmas do not assert original 4.3.16 or the final exceptional-model theorem.
Their final assembly remains with the nonblock endgame sieve owner.
Source: Aschbacher–Smith, original 4.3.16, printed p.618.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The established exclusions remove rows (1) and (3) on the actual action. -/
theorem SecondaryData.nonexceptional_is_unitary (s : SecondaryData c n)
    (hm : NonexceptionalModel (s.component ⧸ pCore 2 s.component) n) :
    IsSU (s.component ⧸ pCore 2 s.component) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 (2 ^ n) := by
  rcases hm with ⟨i,_,hi⟩ | hu | ⟨hn,ht | hj⟩
  · exact (SecondaryData.not_binary_model s (2 ^ i * n) hi).elim
  · exact hu
  · exact (SecondaryData.not_ternary_five_model s hn ht).elim
  · exact (SecondaryData.not_janko_model s hn hj).elim

/-- Conditional reduction of the source alternatives, retaining the outer-action clause. -/
theorem SecondaryData.unitary_or_exceptional_of_source_alternatives (s : SecondaryData c n)
    (hm : SecondaryData.SourceAlternatives s) :
    (IsSU (s.component ⧸ pCore 2 s.component) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 (2 ^ n)) ∨
    (ExceptionalModel (s.component ⧸ pCore 2 s.component) n ∧
      SecondaryData.torusImage s ⊓ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥) := by
  exact hm.imp (SecondaryData.nonexceptional_is_unitary s) id

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
