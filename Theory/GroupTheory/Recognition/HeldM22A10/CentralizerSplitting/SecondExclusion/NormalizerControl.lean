module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Structure
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Context
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.NormalizerControl.Transfer
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.NormalizerControl.ExceptionalAction
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.NormalizerControl.SquareObstruction

/-!
# Exceptional normalizer control in the second Held case

The alternative index-two character of the second local model has a kernel
whose involutions are squares or conjugates of the marked outer involution.
An element normalizing the exceptional subgroup and moving the central
involution fuses the outer involution to a square and forces the order-sixteen
subgroup's normalizer to have order divisible by seven. That divisibility
obstructs an ambient square root of the marked outside involution, contradicting
the transfer argument. Thus the exceptional subgroup's ambient normalizer lies
in the original involution centralizer.

`normalizer_le` discharges both premises of the conditional assembly theorem
using `ExceptionalAction` and `SquareObstruction`. It retains the actual
centralizer equivalence and all original local data. The final second-model
exclusion and the source splitting theorem are assembled separately.

Source problem: Huppert--Blackburn, *Finite Groups III*, XII.1.18(b),
printed p.314; D. Held, J. Algebra 8 (1968), 436--449,
DOI 10.1016/0021-8693(68)90054-9.
-/

namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl
open Subgroup NonsplitModels

/-- The two remaining ambient assertions suffice for normalizer control.
This is a conditional assembly theorem, not the unconditional source result. -/
public theorem normalizer_le_of_action_and_square_obstruction
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (D : LocalData G) (e : D.centralizer ≃* Second)
    (haction : ∀ g : G,
      g ∈ normalizer (ambientExceptionalSubgroup D e : Set G) → g ∉ D.centralizer →
      7 ∣ Nat.card (normalizer (ambientFourGroup D e : Set G)) ∧
        IsConj (embedding D e outerPoint) (embedding D e squarePoint))
    (hsquare : 7 ∣ Nat.card (normalizer (ambientFourGroup D e : Set G)) →
      ¬ ∃ r : G, r ^ 2 = embedding D e outsidePoint) :
    normalizer (ambientExceptionalSubgroup D e : Set G) ≤ D.centralizer := by
  intro g hg
  by_contra hmove
  obtain ⟨hseven, hfusion⟩ := haction g hg hmove
  exact false_of_outer_fusion_of_no_outside_square D e hfusion (hsquare hseven)

/-- The ambient normalizer of the concrete exceptional subgroup lies in the
original involution centralizer. Both ambient proof obligations are discharged. -/
public theorem normalizer_le
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (D : LocalData G) (e : D.centralizer ≃* Second) :
    normalizer (ambientExceptionalSubgroup D e : Set G) ≤ D.centralizer := by
  exact normalizer_le_of_action_and_square_obstruction D e
    (exceptional_action D e) (SquareObstruction.no_outside_square_of_seven_dvd D e)

end Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl
