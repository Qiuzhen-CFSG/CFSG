module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveExclusionsUnitary
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveRowReduction

/-!
# The complete nonexceptional-row exclusions in the nonblock sieve

The proved binary, unitary, PSL₃(5) and J₁ exclusions rule out every
nonexceptional model on the literal secondary configuration. They discharge
both older row-exclusion interfaces and reduce the original four-row
proposition to the two exceptional models, preserving its outer-action clause.

The final reduction still assumes `SourceAlternatives`: it is not a proof
of the source model inspection. Its prime-rank restrictions and alternatives
remain obligations of `qt-d-1222-nonblock-endgame-sieve`, which also owns
unconditional assembly. Source: Aschbacher–Smith, original 4.3.16 and its
first elimination paragraph, printed p.618.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- All three nonexceptional source rows are excluded on the actual configuration. -/
theorem SecondaryData.not_nonexceptional_model (s : SecondaryData c n) (hn : 1 < n) :
    ¬ NonexceptionalModel (s.component ⧸ pCore 2 s.component) n := by
  intro hm
  exact SecondaryData.not_unitary_model s hn (SecondaryData.nonexceptional_is_unitary s hm)

/-- The complete row exclusions discharge the earlier core-centrality interface. -/
theorem SecondaryData.coreImageCentral_of_nonexceptional (s : SecondaryData c n) (hn : 1 < n)
    (hm : NonexceptionalModel (s.component ⧸ pCore 2 s.component) n) :
    SecondaryData.CoreImageCentral s :=
  (SecondaryData.not_nonexceptional_model s hn hm).elim

/-- The complete row exclusions discharge the earlier prime-centralizer interface. -/
theorem SecondaryData.excludedCentralizers (s : SecondaryData c n) (hn : 1 < n) :
    SecondaryData.ExcludedCentralizers s := by
  intro hm
  exact (SecondaryData.not_nonexceptional_model s hn hm).elim

/-- Conditional source assembly; the four-row model inspection remains explicit. -/
theorem SecondaryData.exceptional_of_source_alternatives (s : SecondaryData c n) (hn : 1 < n)
    (hm : SecondaryData.SourceAlternatives s) :
    ExceptionalModel (s.component ⧸ pCore 2 s.component) n ∧
      SecondaryData.torusImage s ⊓ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥ :=
  hm.resolve_left (SecondaryData.not_nonexceptional_model s hn)
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
