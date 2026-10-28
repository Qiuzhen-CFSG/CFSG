module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveModelsOuter
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieve

/-!
# Source-record application of the corrected nonblock sieve

The corrected secondary witness supplies every local-image geometry clause
on its literal normalQuotientAction. The checked core-movement row arguments
exclude binary PSL₂, both unitary forms, J₁ and PSL₃(5), provided the same
whole-radical generation identity is supplied. The exceptional models then
force the original torus to act outerly by the prime-rank argument.

The final theorem is conditional on four-row model inspection and generation.
It discharges the earlier centrality, prime-centralizer and outer-action
premises, but is not the unconditional 4.3.16 classification. The sieve owner
retains model inspection; the nonblock source owner retains construction and
whole-radical generation. No conversion to legacy SecondaryData is used.
Source: Aschbacher--Smith, original 4.3.12--16, printed pp.617--618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}
namespace SecondaryActionData
/-- The four source model rows, retaining the exceptional outer-action clause. -/
def SourceAlternatives (s : SecondaryActionData c n) : Prop :=
  NonexceptionalModel (s.component ⧸ pCore 2 s.component) n ∨
    (ExceptionalModel (s.component ⧸ pCore 2 s.component) n ∧
      torusImage s ⊓ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥)

/-- The actual model gives the exceptional outer clause; it need not be assumed. -/
theorem sourceAlternatives_of_model_alternatives (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hm : NonexceptionalModel (s.component ⧸ pCore 2 s.component) n ∨
      ExceptionalModel (s.component ⧸ pCore 2 s.component) n) : SourceAlternatives s := by
  rcases hm with hm | hm
  · exact Or.inl hm
  · exact Or.inr ⟨hm,exceptional_model_outer_torus s D h hm⟩

/-- Source-correct counterpart of the legacy conditional sieve. Model inspection
and whole-radical generation are the only remaining mathematical inputs. -/
theorem exceptional_of_source_inputs (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1 < n) (hg : ActionGeneration s)
    (hm : NonexceptionalModel (s.component ⧸ pCore 2 s.component) n ∨
      ExceptionalModel (s.component ⧸ pCore 2 s.component) n) :
    (n = 2 ∧ (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4 ∨
      ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)) ∧
      torusImage s ⊓ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥ := by
  rcases sourceAlternatives_of_model_alternatives s D h hm with hm | hm
  · exact (not_nonexceptional_of_generation s hn hg hm).elim
  · exact hm

end SecondaryActionData
