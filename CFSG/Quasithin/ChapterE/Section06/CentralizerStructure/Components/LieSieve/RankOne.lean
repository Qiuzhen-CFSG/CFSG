module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Geometry
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.ActionReduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Placement
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.LinearAction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.SuzukiAction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.UnitaryAction

/-!
# Rank-one components in E.6.8

`exists_borelAlternative` proves all clauses of E.6.8(1) for the three
Bender models away from PSL₂(4). The indexed `borelAlternative_of_model`
retains the given field exponent and actual model equivalence; for PSU₃
the exponent refers to the fixed field, whose square is the matrix-field order.

The component action supplies the marked Sylow subgroup L ∩ C_T(V).
`Geometry` and `Placement` identify its normalizer with L ∩ M, including
when C_T(V) permutes components. The linear, unitary and Suzuki calculations
identify the fixed subgroup, displacement order and actual cyclic induced
action. `ActionReduction` then gives the direct decomposition, exact action
corank, displacement dimension and corank bound.

Only the earlier local facts and the universally quantified E.6.7 source
statement remain explicit inputs. Borel placement and every model calculation
are discharged here. The source treats the excluded PSL₂(4) overlap as PSL₂(5)
in its separate odd alternative.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
open InvariantSubspaces.BlockSelection

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V U L : Subgroup G} {n : ℕ}

/-- The rank-one alternative with its model exponent retained. The actual
Sylow witness, Borel placement and all three action clauses are constructed
from the source inputs; no Borel or action conclusion is assumed. -/
theorem borelAlternative_of_model
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (earlier : EarlierLocalFacts T)
    (h67 : E67Input T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : Model L n) (notFour : ¬ ClassicalGroup.IsPSL L 2 4) :
    BorelAlternative M V U L n := by
  obtain ⟨_, S, hS, _⟩ := component_sylow_action h hU hL rfl
  have hB := sylowBorel_eq_intersection h earlier h67 hU hL hm notFour S hS
  have ha : ActionCalculation M V L n := by
    cases hm with
    | linear hn iso => exact linear_actionCalculation h earlier hU hL hn iso S hS hB
    | unitary hn iso =>
      exact UnitaryAction.calculation_of_isPSU h earlier hU hL hn iso S hS hB
    | suzuki m hm hn iso =>
      obtain ⟨e⟩ := iso
      subst n
      exact suzuki_action_calculation h earlier hU hL hm e S hS hB
  exact borelAlternative_of_calculation h earlier hU hL hm S hS
    (hB.le.trans inf_le_right) ha

/-- E.6.8(1) for every actual Bender model except PSL₂(4), with the exact
earlier E.6.7 statement explicit. This supplies the rank-one branch of the
component sieve, preserving all seven fields of `BorelAlternative`. -/
theorem exists_borelAlternative
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (earlier : EarlierLocalFacts T)
    (h67 : E67Input T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassificationModels.IsBenderModel L)
    (notFour : ¬ ClassicalGroup.IsPSL L 2 4) :
    ∃ n, BorelAlternative M V U L n := by
  obtain ⟨n, hn⟩ := exists_model hm
  exact ⟨n, borelAlternative_of_model h earlier h67 hU hL hn notFour⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
