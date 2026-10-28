module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameUnitarySourceMarking
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoverageApplications

/-!
# The linear-four survivor of the corrected source sieve

Whole-radical generation feeds the same normalQuotientAction into the source
sieve. The actual quintic Sylow-center construction and four-factor bound
exclude PSU₃(5), leaving PSL₃(4) with the original torus still outer.

The sieve owner's model inspection and row exclusions remain explicit inputs.
Construction of MSData and secondary geometry, and the terminal PSL₃(4)
representation argument, remain with the nonblock source assembly owner.
Source: Aschbacher--Smith, conclusion of original 4.3.2, pp.618--619.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SecondarySourceData
open EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- Apply the corrected sieve and eliminate its unitary-five survivor with the
actual extraspecial marking and radical bound. The only surviving quotient is
PSL₃(4), retaining the original torus's outer-action clause. The independent
sieve inputs and the original MS/root geometry remain explicit. -/
theorem linearFour_of_model_inputs (s : SecondarySourceData c n)
    (d : MSData c n) (m : RootCoordinates d) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hm : NonexceptionalModel (s.component ⧸ pCore 2 s.component) n ∨
      (ExceptionalModel (s.component ⧸ pCore 2 s.component) n ∧
        (s.torus.subgroupOf (rootNormalizer c)).map s.action ⊓
          MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥))
    (hc : NonexceptionalModel (s.component ⧸ pCore 2 s.component) n →
      (((secondary c).pCoreIn 2).subgroupOf (rootNormalizer c)).map s.action ≤
        centralizer (((secondary c).subgroupOf (rootNormalizer c)).map s.action : Set _))
    (he : NonexceptionalModel (s.component ⧸ pCore 2 s.component) n →
      ∀ p : ℕ, p.Prime → Odd p → p ∣ 2 ^ n - 1 →
      ∀ a ∈ (s.torus.subgroupOf (rootNormalizer c)).map s.action,
        a ∈ centralizer (((secondary c).subgroupOf (rootNormalizer c)).map s.action : Set _) →
          orderOf a ≠ p) :
    n = 2 ∧ ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4 ∧
      (s.torus.subgroupOf (rootNormalizer c)).map s.action ⊓
        MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥ := by
  obtain ⟨⟨hn2, hmodel⟩, houter⟩ := s.exceptional_of_model_inputs d m hn D hm hc he
  subst n
  rcases hmodel with hlinear | hunitary
  · exact ⟨rfl, hlinear, houter⟩
  · exact (SourceEndgame.unitaryFive_false_of_source_data d s m D h hunitary).elim

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SecondarySourceData
