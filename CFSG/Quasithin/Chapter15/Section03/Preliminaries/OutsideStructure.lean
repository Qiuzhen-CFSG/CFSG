module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalControl
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.OddCore
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.BaumannCentralizing
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.ThetaObstruction

/-!
# Assembly boundary for the twelve outside-overgroup conclusions

The target `OutsideStructure.Conclusions` retains all clauses of 15.3.11.
The completed arguments prove (7) and (12) from the precise earlier inputs,
reduce (1) to the natural-action noncentrality of Y₊, and prove (2),(4) in
the first choice. Two-perfectness of both choices is derived from the actual
residual construction. Local normalizer control handles the remaining steps
of (2)–(4) once the second choice's residual and action calculations are known.

The quotient argument already proves (9) from (2),(4),(6) and nontrivial
action. The centralizing branch of (10), and (11) after the noncentral
commutator identity, are proved in the imported modules. The final odd-core
step and every rank hypothesis needed for A.1.26(1) are also proved.

The full conclusion still requires the two local-structure alternatives,
theta identification, the noncentral Thompson calculation, the centralizing
Frattini step, and source A.1.26(1). None is assumed through an inhabitant of
the target record. Final assembly of this lemma stays here; the enclosing
Preliminaries owner must discharge the allowed 15.3.2–9 inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11, printed pp.1123–1124 (PDF pp.1140–1141).
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure
open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- Clause (1) under the actual construction and Hypothesis 15.3.10.
Only the noncentral natural action remains beyond the displayed earlier
15.3.2(4), stabilizer-index, and 15.3.6(2) inputs. -/
theorem lemma_15_3_11_1_of_nontrivial_action (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hN : normalizer (d.S : Set G) ≤ d.M)
    (h24 : ∀ X : Subgroup G, (d.T : Subgroup G) ≤ X → X ≤ d.M →
      twoResidualAmbient X ≤ d.M ⊓ centralizer (d.V : Set G) ∨
        Chapter4.UniqueMaximalOvergroup X d.M)
    (hact : ¬ d.Yplus ≤ centralizer (d.V : Set G)) :
    ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S := by
  have hYM : d.Yplus ≤ d.M :=
    (choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice).trans
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)
  exact lemma_15_3_11_1_of_action d.T d.M d.V d.Yplus d.S I d.sylow_le hYM
    inf_le_left hindex hN d.action.normalizes h24
    (chosen_residual_eq d.M d.Mc d.S d.V₁ d.Yplus d.choice) hact hI

/-- Clause (7) from the standing even-characteristic hypothesis and the
index-two stabilizer. This is the full generalized Fitting equality. -/
theorem lemma_15_3_11_7 (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus)
    (hE : IsEvenCharacteristicAt d.T) (hM : IsMaximalTwoLocal d.M)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2) :
    Theory.GroupTheory.generalizedFitting (d.MI I) = pCore 2 (d.MI I) :=
  (lemma_15_3_11_7_of_index_two d.T d.M d.S I d.sylow_le inf_le_left
    (le_sup_right.trans hI.1.2) hindex (hE d.M hM d.sylow_le)).2

/-- Clause (12) under the actual residual construction. The earlier uniqueness
dichotomy is applied to O²(Y∩L)T; no characteristic-normality premise is
hidden in the standing local data. The proof does not require L ≤ I. -/
theorem lemma_15_3_11_12 (d : CharacteristicTwo.LocalData G)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (h24 : ∀ X : Subgroup G, (d.T : Subgroup G) ≤ X → X ≤ d.M →
      twoResidualAmbient X ≤ d.M ⊓ centralizer (d.V : Set G) ∨
        Chapter4.UniqueMaximalOvergroup X d.M)
    (L : Subgroup G) (hact : ⁅d.V, twoResidualAmbient (d.Y ⊓ L)⁆ ≠ ⊥)
    (hL : ¬ L ≤ d.M) (C : Subgroup d.S) [C.Characteristic] (hC : C ≠ ⊥) :
    ¬ ((C.map d.S.subtype).subgroupOf (L ⊔ d.S)).Normal :=
  lemma_15_3_11_12_of_preliminary_uniqueness d.T d.M d.V d.Y d.S L d.sylow_le
    (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) inf_le_left hindex h24
    hact hL C hC

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure
end
