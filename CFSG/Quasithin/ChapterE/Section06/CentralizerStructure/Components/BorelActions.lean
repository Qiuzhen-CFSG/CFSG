module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.Reduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.LinearTwo
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.Suzuki
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.LinearThree
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.UnitaryThree
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.Singer

/-!
# Borel component torus actions in E.6.11

`conclusion_of_borelAlternative` constructs the cyclic complement in every
Borel model of E.6.8(1), including all central two-covers of PSL₃(4). The model
calculations supply the complement and Sylow-center bound; `Reduction`
identifies its displacement and proves faithfulness. Binary Singer regularity
then gives regular conjugation on the nonidentity displacement elements.

This is the intrinsic Borel contract used in E.6.11. The component sieve and
source assembly must supply the E.6.8 alternative, normalization by V, and the
actual Sylow subgroup with ambient image L ∩ Q. No maximality of U or normality
of L in its centralizer overgroup is assumed here. The unitary model retains
fixed-field order 2ⁿ and matrix-field order 2²ⁿ.

Source: Aschbacher–Smith, E.6.8(1) and E.6.11, printed pp.247,249–250.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.BorelActions

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G} {n : ℕ}

/-- Conditional assembly of the intrinsic Borel contract. The model
computations must construct `model`, and the independent cyclic-action
argument must supply `singer`, before this proves the requested contract. -/
theorem conclusion_of_modelWitness
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (b : BorelAlternative M V U L n) (hn : 1 < n)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (model : ModelWitness M V Q L n) (singer : BinarySingerRegularity (G := G)) :
    BorelTorusConclusion M V Q L n := by
  obtain ⟨X, hX, hcyc, hgen, hdis⟩ := model.exists_complement
  have heq := displacement_eq_of_complement h hU hL hX hgen
  have hreg := singer ⁅V, L ⊓ M⁆ X n hn (displacement_elementary h b hn)
    (displacement_card h b hn) hcyc
    (hX.trans (normalizer_commutator_ge_right V (L ⊓ M)))
    (complement_faithful b hn hX hdis)
  refine ⟨X, ⟨hX, hcyc, hgen, hdis, heq, ?_⟩, ?_⟩
  · simpa only [heq] using hreg
  · rw [heq]
    exact le_antisymm (core_sup_displacement_le_center h hU hL hVL hQ S hS)
      model.center_le

/-- Every Borel model in E.6.8(1) supplies the embedded cyclic complement and
the remaining Sylow-center bound, including every central two-cover of PSL₃(4). -/
theorem modelWitness_of_borelAlternative
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (b : BorelAlternative M V U L n) (hn : 1 < n)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q) :
    ModelWitness M V Q L n := by
  cases b.model with
  | linear_two _ iso =>
      exact modelWitness_linear_two h hU hL b hn hVL hQ S hS iso
  | suzuki m hm hnm iso =>
      obtain ⟨e⟩ := iso
      exact modelWitness_suzuki h hU hL b hn hVL hQ S hS m hm hnm e
  | linear_three _ iso =>
      exact modelWitness_linear_three h hU hL b hn hVL hQ S hS iso
  | unitary_three _ iso =>
      exact modelWitness_unitary_three h hU hL b hn hVL hQ S hS iso
  | linear_three_cover hn2 hz iso =>
      exact modelWitness_linear_three_cover h hU hL b hn hVL hQ S hS hn2 hz iso

/-- The Borel case supplies an actual cyclic complement to C_L(V), regular
conjugation on its displacement, and O₂(L)[V,X] = Z(L ∩ Q) as ambient subgroups.
All model and Singer-action obligations are discharged; only the explicitly
stated E.6 setup, alternative, normalization and Sylow placement are inputs. -/
theorem conclusion_of_borelAlternative
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (b : BorelAlternative M V U L n) (hn : 1 < n)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q) :
    BorelTorusConclusion M V Q L n :=
  conclusion_of_modelWitness h hU hL b hn hVL hQ S hS
    (modelWitness_of_borelAlternative h hU hL b hn hVL hQ S hS)
    binarySingerRegularity

end CFSG.Quasithin.ChapterE.Section06.Components.BorelActions
