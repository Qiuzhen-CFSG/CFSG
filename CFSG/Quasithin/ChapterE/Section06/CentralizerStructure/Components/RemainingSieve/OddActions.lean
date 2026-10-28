module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceInputs
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.OddActions.ActionBounds
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.OddActions.Covers
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.OddActions.MathieuCover
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.OddActions.SmallModelFixers
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.OddActions.SourceAction

/-!
# The odd-action branch of the remaining E.6.8 sieve

The actual V-conjugation image fixes the component's Sylow intersection.
The PSL₂, PSL₃(3), and M₁₁ fixer calculations bound that image by two, with
the PSL₂ small-prime exclusions justified by perfection and actual models.
The proved Mathieu cover calculation first identifies the original L with
M₁₁ in the sporadic branch. E.6.6 then makes the action nontrivial, and the
weak-closure inequality gives both rank-one equalities.

The two source-branch exports give the separately adopted adequate odd tuple:
the original model on L, action corank one, and global rank one. They retain
the literal source conjugation and inner-action inputs; the bounds hold for
the entire Sylow-fixing action image, so these extra action restrictions are
not needed again in the estimates. The equality U = C_V(L) in the full
`OddAlternative` is a separate obligation and is not asserted here. The parent
remaining sieve owns the other 1.1.5 cases and final assembly. The PSL₂(4)
endpoint in the Lie sieve is also separate.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
E.6.8(5), printed p.248, and 1.1.5(3)(e,f), printed pp.502–503.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.OddActions
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- The entire odd linear source family has action corank at most one. -/
theorem odd_actionCorank_le_one (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hnotLie : ¬ LieTypeComponent L)
    (hmodel : ClassicalGroup.IsPSL L 3 3 ∨
      ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p) :
    actionCorank V L ≤ 1 := by
  rcases hmodel with hm | ⟨p, hp, hm⟩
  · exact linear_three_three_actionCorank_le_one h hU hL hm
  · exact odd_linear_actionCorank_le_one h hU hL hnotLie hp hm

/-- The M₁₁ source quotient gives both the actual model of L and its action bound.
The multiplier premise of the earlier cover reduction is fully discharged. -/
theorem m11_model_and_actionCorank_le_one (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hmodel : Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M11)) :
    Nonempty (L ≃* Sporadic.Mathieu.M11) ∧ actionCorank V L ≤ 1 := by
  obtain ⟨e⟩ := component_m11_model hL hmodel
  exact ⟨⟨e⟩, m11_actionCorank_le_one h hU hL e⟩

/-- The adequate odd tuple in the genuine `ModelAction115.odd` branch.
The model and innerness arguments are exactly that constructor's fields. -/
theorem adequate_of_odd_action (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hnotLie : ¬ LieTypeComponent L)
    {z : G} (_hz : z ∈ sylowFixedSpace (T : Subgroup G) V)
    {α : MulAut L} (_hconj : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hmodel : ClassicalGroup.IsPSL L 3 3 ∨
      ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p)
    (_hinner : α ∈ (MulAut.conj (G := L)).range) :
    ((∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p) ∨
      ClassicalGroup.IsPSL L 3 3 ∨ Nonempty (L ≃* Sporadic.Mathieu.M11)) ∧
      actionCorank V L = 1 ∧ globalR V = 1 := by
  refine ⟨?_, rank_one_of_action_bound h (component_not_le h earlier hU hL)
    (odd_actionCorank_le_one h hU hL hnotLie hmodel)⟩
  exact hmodel.elim (fun hm => Or.inr (Or.inl hm)) Or.inl

/-- The adequate odd tuple in `ModelAction115.sporadic` with name M₁₁.
The quotient and two-central inner action are the literal constructor fields;
cover elimination precedes the application of the M₁₁ action bound. -/
theorem adequate_of_m11_action (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {z : G} (_hz : z ∈ sylowFixedSpace (T : Subgroup G) V)
    {α : MulAut L} (_hconj : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hmodel : Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M11))
    (_haction : TwoCentralInner α) :
    ((∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p) ∨
      ClassicalGroup.IsPSL L 3 3 ∨ Nonempty (L ≃* Sporadic.Mathieu.M11)) ∧
      actionCorank V L = 1 ∧ globalR V = 1 := by
  obtain ⟨hm, hb⟩ := m11_model_and_actionCorank_le_one h hU hL hmodel
  exact ⟨Or.inr (Or.inr hm),
    rank_one_of_action_bound h (component_not_le h earlier hU hL) hb⟩

end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.OddActions
