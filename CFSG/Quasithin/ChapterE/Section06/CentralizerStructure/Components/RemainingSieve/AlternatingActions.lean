module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceInputs
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.AlternatingActions.Six
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.AlternatingActions.Seven

/-!
# Assembly for the alternating branch of E.6.8

The intrinsic action calculations have two outputs: an action image of order
at most four, and generation by the fixed subgroups of its nonidentity elements
when that image has order four. The transport lemmas turn these into the source
corank bound and hyperplane generation. The existing reduction then constructs
an escaping hyperplane and proves r(G,V) = 1.

The six- and seven-letter calculations are discharged using the actual
Sylow-fixing conjugation image. The direct A6 case is excluded by the polar
isomorphism and the remaining-sieve hypothesis; the genuine triple A6 cover,
A7, and triple A7 cover give both action facts. The two source-branch theorems
therefore supply all clauses of E.6.8(4), without assuming a corank bound or
an escaping hyperplane. The parent sieve supplies the model action from
1.1.5(3) and owns the other cases of that theorem.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.6.8(4),
printed pp.247--248, using the model alternatives in 1.1.5(3)(c,d), pp.501--502.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.AlternatingActions
open Chapter1.Section02.LocalModels
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- Assemble E.6.8(4) after the intrinsic model calculations. Both additional
premises refer to the actual conjugation image; neither an escaping hyperplane
nor the source dimension bound is taken as input. The source-branch theorems
below discharge the model calculations in the six- and seven-letter cases. -/
theorem alternating_of_image_calculations (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : V ≤ normalizer (L : Set G))
    (hmodel : IsAlternating L 7 ∨ IsAlternatingCover L 6 ∨ IsAlternatingCover L 7)
    (hcard : Nat.card (actionHom hn).range ≤ 4)
    (hgen : Nat.card (actionHom hn).range = 4 →
      (⊤ : Subgroup L) ≤ ⨆ (a : (actionHom hn).range) (_ : a ≠ 1),
        fixedSubgroup (a : MulAut L)) :
    AlternatingAlternative M V U L := by
  let _ := h.elementary
  apply alternating_of_action_facts h hU.1 hL.1 (component_not_le h earlier hU hL)
    hmodel (actionCorank_le_two_of_card_range_le_four hn hcard)
  intro hd
  have hc := card_range_eq_four_of_actionCorank_two hn hd
  exact hyperplane_generation_of_fixedSubgroup_generation hn hU.1 hL.1 hc (hgen hc)

/-- Convert the two intrinsic image calculations into the exact ambient
corank bound and generation over hyperplanes containing U. -/
private theorem action_facts_of_image_calculations [IsElementaryAbelian 2 V]
    (hUV : U ≤ V) (hLH : L ≤ centralizer (U : Set G))
    (hn : V ≤ normalizer (L : Set G))
    (hcard : Nat.card (actionHom hn).range ≤ 4)
    (hgen : Nat.card (actionHom hn).range = 4 →
      (⊤ : Subgroup L) ≤ ⨆ (a : (actionHom hn).range) (_ : a ≠ 1),
        fixedSubgroup (a : MulAut L)) :
    actionCorank V L ≤ 2 ∧ (actionCorank V L = 2 →
      L ≤ ⨆ (A : Subgroup G) (_ : U ≤ A) (_ : A ≤ V)
        (_ : subgroupCorank V A = 1), L ⊓ centralizer (A : Set G)) := by
  refine ⟨actionCorank_le_two_of_card_range_le_four hn hcard, ?_⟩
  intro hd
  have hc := card_range_eq_four_of_actionCorank_two hn hd
  exact hyperplane_generation_of_fixedSubgroup_generation hn hUV hLH hc (hgen hc)

/-- The transposition case of 1.1.5(3)(c) gives the action bound and ambient
hyperplane generation. The characteristic-two exclusion removes only direct A6;
the calculation retains the actual triple cover and intertwined quotient map. -/
theorem six_action_facts (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hnotLie : ¬ LieTypeComponent L)
    {z : G} (hz : z ∈ sylowFixedSpace (T : Subgroup G) V)
    {α : MulAut L} (hconj : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    {σ : Equiv.Perm (Fin 6)} (hσ : σ.IsSwap) (ha : AlternatingAction α 6 σ) :
    actionCorank V L ≤ 2 ∧ (actionCorank V L = 2 →
      L ≤ ⨆ (A : Subgroup G) (_ : U ≤ A) (_ : A ≤ V)
        (_ : subgroupCorank V A = 1), L ⊓ centralizer (A : Set G)) := by
  let _ := h.elementary
  have hn := component_normalized h hU hL
  let _ := range_elementary hn
  obtain ⟨S, hfix⟩ := exists_sylow_fixed_by_range h hU hL hn
  have hα := mem_range_of_action hz.1 hn α hconj
  rcases ha with ⟨e, _⟩ | ⟨hq, hZ, e, haction⟩
  · exact (hnotLie (lieType_of_alternating_six ⟨e⟩)).elim
  · let _ : IsQuasisimple L := hq
    obtain ⟨hcard, hgen⟩ := six_cover_image_calculations hZ e
      (actionHom hn).range S hfix α hα σ hσ haction
    exact action_facts_of_image_calculations hU.1 hL.1 hn hcard hgen

/-- The triple-transposition case of 1.1.5(3)(d) gives the same two action
facts for both the actual A7 model and its genuine triple cover. -/
theorem seven_action_facts (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {z : G} (hz : z ∈ sylowFixedSpace (T : Subgroup G) V)
    {α : MulAut L} (hconj : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    {σ : Equiv.Perm (Fin 7)} (hσ : σ.cycleType = {2, 2, 2})
    (ha : AlternatingAction α 7 σ) :
    actionCorank V L ≤ 2 ∧ (actionCorank V L = 2 →
      L ≤ ⨆ (A : Subgroup G) (_ : U ≤ A) (_ : A ≤ V)
        (_ : subgroupCorank V A = 1), L ⊓ centralizer (A : Set G)) := by
  let _ := h.elementary
  have hn := component_normalized h hU hL
  let _ := range_elementary hn
  obtain ⟨S, hfix⟩ := exists_sylow_fixed_by_range h hU hL hn
  have hα := mem_range_of_action hz.1 hn α hconj
  obtain ⟨hcard, hgen⟩ := seven_image_calculations
    (actionHom hn).range S hfix α hα σ hσ ha
  exact action_facts_of_image_calculations hU.1 hL.1 hn hcard hgen

/-- E.6.8(4) in the six-letter source branch, with every intrinsic action
premise discharged and the escaping hyperplane and global rank constructed. -/
theorem alternating_of_six_action (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hnotLie : ¬ LieTypeComponent L)
    {z : G} (hz : z ∈ sylowFixedSpace (T : Subgroup G) V)
    {α : MulAut L} (hconj : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    {σ : Equiv.Perm (Fin 6)} (hσ : σ.IsSwap) (ha : AlternatingAction α 6 σ) :
    AlternatingAlternative M V U L := by
  obtain ⟨hd, hgen⟩ := six_action_facts h hU hL hnotLie hz hconj hσ ha
  exact alternating_of_action_facts h hU.1 hL.1 (component_not_le h earlier hU hL)
    (Or.inr (Or.inl (three_cover_of_six_action ha hnotLie))) hd hgen

/-- E.6.8(4) in the seven-letter source branch. Both possible centers and the
literal cycle-type action are preserved through the intrinsic calculation. -/
theorem alternating_of_seven_action (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {z : G} (hz : z ∈ sylowFixedSpace (T : Subgroup G) V)
    {α : MulAut L} (hconj : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    {σ : Equiv.Perm (Fin 7)} (hσ : σ.cycleType = {2, 2, 2})
    (ha : AlternatingAction α 7 σ) :
    AlternatingAlternative M V U L := by
  obtain ⟨hd, hgen⟩ := seven_action_facts h hU hL hz hconj hσ ha
  have hmodel : IsAlternating L 7 ∨ IsAlternatingCover L 6 ∨ IsAlternatingCover L 7 :=
    (model_of_seven_action ha).imp_right Or.inr
  exact alternating_of_action_facts h hU.1 hL.1 (component_not_le h earlier hU hL)
    hmodel hd hgen

end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.AlternatingActions
