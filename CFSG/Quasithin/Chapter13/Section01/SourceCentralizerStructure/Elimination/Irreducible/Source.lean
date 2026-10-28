module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Source

/-!
# Source assembly of the irreducible centralizer branch

The original module classification supplies either the quaternion actions
or the actual S₃ quotient of the component stabilizer. The completed ordinary
and characteristic-two exclusions apply to these two alternatives. In
particular, the deleted S₅ module uses its S₃ quotient directly; no universal
`SieveActions` premise or unproved linear-three parabolic marking is needed.
All component, two-core quotient, central quotient and star-image carriers
remain those of the original selected involution.

This module connects that source construction to the component-exclusion
consumer and its TI application. Thompson movement is the earlier 13.1.9
premise produced by qt-d-1317-supplements and discharged by qt-d-1317-source.
Control and the separate reducible component-normalizer branch remain with
qt-d-1317-centralizer-sieve, whose final assembly uses these exports. The
irreducible branch has no remaining module, model or local exclusion premise.

Source: Aschbacher–Smith, 13.1.12(3)–13, printed pp.874–875; the module
classification and selected-representative actions are on pp.871–873.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02
open SourceNonquasisimple.ModuleOrbits
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The source irreducible branch, with the earlier module actions constructed
from Thompson movement. The symmetric-five row uses its literal S₃ quotient. -/
theorem Context.not_escape_of_irreducible_source (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) : False := by
  rcases Classification.source_inputs_or_symmetric h hmove with ha | hs
  · exact h.not_escape_of_irreducible_source_actions ha.2 c s hnt e hi
  · exact not_escape_of_irreducible_symmetricThree h c s hnt e hi
      (hs.some.symmetricThreeStabilizerQuotient h s hnt)

/-- Apply the source irreducible exclusion to the literal centralizer
consumer. Only the independently owned reducible branch remains. -/
theorem Context.centralizer_le_of_source_irreducible (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (c : Control T L p)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False)
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    centralizer ({u} : Set G) ≤ normalizer (L : Set G) :=
  h.centralizer_le_of_component_exclusions (Classification.orbitFacts_of_source h hmove) c
    (fun _ s hnt _ e hi => h.not_escape_of_irreducible_source hmove c s hnt e hi)
    hred hu hne

/-- Original 13.1.13 applied to the completed irreducible branch and the
separate reducible exclusion, using the same original moved subgroup. -/
theorem Context.ti_of_source_irreducible (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (c : Control T L p)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False) :
    ChapterI.Section06To08.IsTISubgroup (normalizerMoved L) ∧
      normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) := by
  apply h.ti_of_selected (Classification.orbitFacts_of_source h hmove)
  intro u s
  exact h.centralizer_le_of_source_irreducible hmove c hred s.mem s.ne_one

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
