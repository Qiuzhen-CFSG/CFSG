module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.Reductions
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Models

/-!
# The earlier source input for the remaining E.6.8 cases

`Earlier115Three` is exactly the ordinary-component assertion of 1.1.5(3),
with the component embedded in the ambient group. Its model/action specification
is reused from `ComponentStructure.Models`; no Chapter 15 theorem is invoked.
The E.6.6 deductions construct its hypotheses with C_G(z) in the role of M.
Thus the M in that earlier theorem is distinct from the M in Hypothesis E.6.1.

The input retains all six alternatives, their actual isomorphisms, central
covers, inner actions, and alternating permutation actions. It is deliberately
an explicit earlier theorem premise, not an assertion that 1.1.5 has been proved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 1.1.5(3),
printed pp.501–503, and the opening of the proof of E.6.8, printed p.247.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve
open Chapter1.Section02.LocalModels
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- Universal source 1.1.5(3) with actual embedded components. The output
uses the exact model/action specification, not an E.6.8 alternative. -/
def Earlier115Three (K : GroupClass) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (_ : IsSimpleQTKE K G) (H : Subgroup G) (S : Sylow 2 H)
    (B : Subgroup G) (z : G), Chapter1.Lemma115Hypotheses H S B z →
    ∀ L : Subgroup G, ComponentIn H L →
      L = ⁅L, zpowers z⁆ ∧ ¬ L ≤ B ∧
        ∃ α : MulAut L, (∀ x : L, (α x : G) = z * (x : G) * z⁻¹) ∧
          ModelAction115 L α

/-- Every nonidentity source fixed point gives the full earlier model/action
alternative. E.6.8 is not assumed in constructing this input. -/
theorem source_model_action (h : HypothesisE61 K T M V)
    (localFacts : EarlierLocalFacts T) (source115 : Earlier115Three K G)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {z : G} (hz : z ∈ sylowFixedSpace (T : Subgroup G) V) (hne : z ≠ 1) :
    L = ⁅L, zpowers z⁆ ∧ ¬ L ≤ centralizer ({z} : Set G) ∧
      ∃ α : MulAut L, (∀ x : L, (α x : G) = z * (x : G) * z⁻¹) ∧
        ModelAction115 L α := by
  obtain ⟨S, _, hinput⟩ := chapterOne_inputs h localFacts hU hz hne
  exact source115 h.simpleQTKE _ S _ z hinput L hL

/-- Existence of a genuine source involution and its actual model action. -/
theorem exists_source_model_action (h : HypothesisE61 K T M V)
    (localFacts : EarlierLocalFacts T) (source115 : Earlier115Three K G)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    ∃ z ∈ sylowFixedSpace (T : Subgroup G) V, z ≠ 1 ∧
      L = ⁅L, zpowers z⁆ ∧ ¬ L ≤ centralizer ({z} : Set G) ∧
        ∃ α : MulAut L, (∀ x : L, (α x : G) = z * (x : G) * z⁻¹) ∧
          ModelAction115 L α := by
  obtain ⟨z, hz, hne⟩ := exists_sylow_fixed h
  exact ⟨z, hz, hne, source_model_action h localFacts source115 hU hL hz hne⟩

omit [Finite G] in
/-- The transposition alternative remaining outside characteristic two must
be the genuine triple cover. The direct A6 action is excluded by its polar
isomorphism, rather than by a family label. -/
theorem three_cover_of_six_action {α : MulAut L} {σ : Equiv.Perm (Fin 6)}
    (ha : AlternatingAction α 6 σ) (hn : ¬ LieTypeComponent L) :
    IsAlternatingCover L 6 := by
  rcases ha with ⟨e, _⟩ | ⟨hq, hz, e, _⟩
  · exact (hn (lieType_of_alternating_six ⟨e⟩)).elim
  · exact ⟨hq, hz, ⟨e⟩⟩

omit [Finite G] in
/-- Both possible centers in the seven-letter source action are retained. -/
theorem model_of_seven_action {α : MulAut L} {σ : Equiv.Perm (Fin 7)}
    (ha : AlternatingAction α 7 σ) :
    IsAlternating L 7 ∨ IsAlternatingCover L 7 := by
  rcases ha with ⟨e, _⟩ | ⟨hq, hz, e, _⟩
  · exact Or.inl ⟨e⟩
  · exact Or.inr ⟨hq, hz, ⟨e⟩⟩

end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve
