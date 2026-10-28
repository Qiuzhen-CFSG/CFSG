module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.WeakClosure
public import CFSG.Quasithin.Chapter13.Section03.LocalSteps
public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses

/-!
# The literal chosen-module consumer of the unitary weak-closure step

The actual module in `Irr⁺(L,R₂(LT),T)` supplies elementary abelianness.
Transitivity and the abelian closure of 13.3.18 supply 13.3.19(1), and the
preceding weak-closure argument proves 13.3.19(2) for this same module and
Sylow subgroup. Its remaining inputs are the earlier bound 13.3.17(2),
T-invariance from 13.3.2, and the binary model row B.4.6(3,9).

These are explicitly named mathematical inputs, not extra exclusions on the
original group or an assumed weak-closure conclusion. The full 13.3.16
assembly must construct the abelian closure and earlier source data.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.3.17–19,
printed pp.894–896.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The original chosen module, with the point-fusion implication discharged. -/
theorem chosen_module_weakClosure_two
    {T : Sylow 2 G} {L V : Subgroup G}
    (d : Chapter12.Section02.ChosenModule T L V)
    (hTN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hV : rank V = 6)
    (z : G) (hz : z ≠ 1)
    (htrans : ∀ x ∈ V, x ≠ 1 → ∃ n ∈ normalizer (V : Set G),
      MulAut.conj n z = x)
    [IsMulCommutative (centralizerConjugateClosure V z)]
    (hr : (3 : ℕ∞) < globalR V)
    (hB46 : letI := d.elementary
      ∀ (A : Subgroup G), A ≤ normalizer (V : Set G) →
      ∀ k : ℕ, 2 ≤ k → inducedAutomizer V A ∈
        fixedSpaceFamily (automizerRepresentation V) k →
      k = 2 ∧ rank (inducedAutomizer V A) = 3 ∧ subgroupCorank V ⁅V,A⁆ ≤ 3) :
    indexedWeakClosure V (T : Subgroup G) 2 ≤ centralizer (V : Set G) := by
  let := d.elementary
  exact weakClosure_two_centralizes_of_unitary_action hTN hV
    (fun g => commuting_conjugates_of_transitive_abelian_closure V z g hz htrans)
    hr hB46

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
