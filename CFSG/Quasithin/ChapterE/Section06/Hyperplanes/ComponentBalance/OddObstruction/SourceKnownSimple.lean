module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.SourceInspection
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceComplete

/-!
# Known-simple E.6.19--22 source assembly

The complete E.6.8 sieve is an actual theorem for `KnownSimple.IsKnownSimple`.
This file discharges that interface at the E.6.19 obstruction boundary, so the
balance, odd-core and characteristic-two consumers retain only the genuine
E.6.18 exclusion and common-normal input.  This is the source-facing route for
the E.6.19--22 chain; no additional model callback is introduced.

Source: Aschbacher--Smith, E.6.8 and E.6.19--22, printed pp.247--254.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes
open Components ComponentBalance Enlargement SignalizerElimination
open ComponentBalance.OddObstruction
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V : Subgroup G}

/-- The complete known-simple E.6.8 output in the obstruction interface. -/
theorem adequate_models_knownSimple
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) :
    ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      AdequateComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X := by
  intro A hA X hX
  exact Components.RemainingSieve.adequateComponentAlternatives_knownSimple h hA
    (show ComponentIn (centralizer (A : Set G)) X from hX)

/-- E.6.19 balance with the known-simple E.6.8 sieve discharged. -/
theorem source_hyperplaneBalance_knownSimple [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (h15 : HypothesisE615 V)
    (h18 : SevenExcluded M V) :
    HyperplaneBalance V :=
  source_hyperplaneBalance h h15 h18 (adequate_models_knownSimple h)

/-- E.6.21 odd-core freeness after the known-simple E.6.8 sieve. -/
theorem source_oddCoreFree_knownSimple [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (h15 : HypothesisE615 V)
    (h311 : InvariantSubspaces.CommonNormalInput KnownSimple.IsKnownSimple T)
    (h18 : SevenExcluded M V) :
    OddCoreFree V :=
  source_oddCoreFree h h15 h311 h18 (adequate_models_knownSimple h)

/-- E.6.22 hyperplane characteristic two with E.6.8 discharged. -/
theorem source_hyperplane_characteristicTwo_knownSimple [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (h15 : HypothesisE615 V)
    (h311 : InvariantSubspaces.CommonNormalInput KnownSimple.IsKnownSimple T)
    (h18 : SevenExcluded M V) :
    ∀ U : Subgroup G, IsHyperplane V U →
      generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G)) :=
  source_hyperplane_characteristicTwo_of_model_sources h h15 h311 h18
    (adequate_models_knownSimple h)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes
