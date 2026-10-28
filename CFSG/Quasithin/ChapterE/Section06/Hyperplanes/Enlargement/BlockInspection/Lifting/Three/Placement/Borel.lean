module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Setup
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Borel.LinearTwo
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Borel.LinearThree
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Borel.UnitaryThree

/-!
# The Borel interaction for the solvable A₃ block

The original hyperplane centralizer normalizes the component. Its conjugation
action fixes a noncentral involution and contains an actual inner Sylow
two-subgroup. The original A₃ block embeds subnormally in that actor.

The PSL₂(4) action vanishes by its concrete A₅ automorphism calculation.
For PSL₃(4), the subnormal block centralizes the marked Sylow subgroup,
and the pointwise Sylow-fixer calculation kills its remaining action.
Faithful automorphism descent handles every perfect central two-cover.
For PSU₃(4), the outer two-group makes the action inner, and its fixed
involution has inner centralizer of order prime to three.

The final assembly supplies all model actions and proves BorelInteraction
from E.6.1. The contract already retains the actual E.6.8 Borel alternative
and fixed-space equality; no further E.6.15 or action premise is needed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8 and
the solvable-block gap in E.6.23, printed pp.247–248 and 254–255.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement
open ComponentBalance Components Borel

variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- Conditional assembly retaining every Borel model. The intrinsic action
premises are discharged in `borelInteraction` below. -/
theorem borelInteraction_of_model_actions
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (hlinear : ∀ X : Subgroup G, IsQuasisimple X →
      (ClassicalGroup.IsPSL X 3 4 ∨
        (IsPGroup 2 (center X) ∧ ClassicalGroup.IsPSL (X ⧸ center X) 3 4)) →
      FixedSylowActionTrivial X)
    (hunitary : ∀ X : Subgroup G, IsQuasisimple X → ClassicalGroup.IsPSU X 3 4 →
      FixedSylowActionTrivial X) : BorelInteraction M V := by
  let := h.elementary
  intro U hU hUh L hL h3 _ A hA hAU hc X hX hf b
  right
  apply commutes_of_fixedSylowActionTrivial h hU hUh hL h3 hA hAU hc hX hf b
  have hq : IsQuasisimple X := (show IsComponentIn X (centralizer (A : Set G)) from hX).quasisimple
  rcases ComponentCase.borel_models_at_two b with hm | hm | hm | hm
  · exact linearTwo_fixedSylowActionTrivial hm
  · exact hlinear X hq (Or.inl hm)
  · exact hunitary X hq hm
  · exact hlinear X hq (Or.inr hm)

/-- The original A₃ block commutes with every parameter-four Borel component,
giving the required containing-or-commuting alternative. All model actions,
including those on central two-covers of PSL₃(4), are discharged. -/
theorem borelInteraction
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V) :
    BorelInteraction M V :=
  borelInteraction_of_model_actions h
    (fun _ hq hm => linearThree_fixedSylowActionTrivial hq hm)
    (fun _ _ hm => unitaryThree_fixedSylowActionTrivial hm)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement
