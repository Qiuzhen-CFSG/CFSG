module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Reduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.QuotientAction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CenterOrder
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators

/-!
# Assembling the J₄ two-core linear comparison

The actual quotient action gives the required homomorphism once two concrete
inputs are known: the center of Q = O₂(C) has order two, and the quotient has
binary coordinates in which two elements generating C modulo Q act as the
specified ATLAS matrices. The former and the coordinates make Q extraspecial;
commutator duality proves the kernel bound. Generation then gives the exact
image, without a global order, simplicity, or normalizer premise.

The concrete center-order and coordinate certificates discharge both inputs
for the literal J₄ model. The final comparison retains only centralizer
control, which identifies the kernel of the local quotient action with Q
when proving that the coordinate generators generate C modulo Q.

Source motivation: GLS3, Table 5.3i, printed p.270,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. The centralizer shape in the table does
not substitute for either concrete calculation.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares

/-- Construct the comparison and prove both clauses from the concrete center order,
quotient coordinates, and generator conjugation identities. -/
theorem localTwoCoreLinearComparison_of_center_order_coordinates
    (hcenter : Nat.card (Subgroup.center involutionTwoCore) = 2)
    (d : TwoCoreComparison.ActionGenerators) : LocalTwoCoreLinearComparison := by
  let _ := TwoCoreComparison.extraspecial_of_coordinates hcenter d.coordinates
  refine ⟨TwoCoreComparison.matrixAction d.coordinates,
    (TwoCoreComparison.matrixAction_ker d.coordinates).le, ?_⟩
  exact d.map_range

/-- The automorphism action on the actual central quotient has inner kernel
and maps the literal centralizer action onto the fixed ATLAS matrix group.
The center order, quotient coordinates, and generator actions are all supplied
by concrete certificates; only local centralizer control remains an input. -/
theorem localTwoCoreLinearComparison
    (hcent : LocalTwoCoreCentralizerControl) : LocalTwoCoreLinearComparison := by
  obtain ⟨d⟩ := TwoCoreComparison.nonempty_actionGenerators hcent
    TwoCoreComparison.center_card_two
  exact localTwoCoreLinearComparison_of_center_order_coordinates
    TwoCoreComparison.center_card_two d

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares
