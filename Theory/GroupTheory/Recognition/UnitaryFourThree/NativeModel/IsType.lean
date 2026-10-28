module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.NativeModel.Intersection
public import Theory.GroupTheory.Recognition.UnitaryFourThree.NativeModel.CentralizerOrder

/-!
# The original type U₄(3) witness in the concrete projective unitary group

The native field-nine SU₄ image in PGL, with its literal standard involution,
satisfies every clause of Aschbacher's original type definition: the two
normal SL₂(3) residual factors, the marked core and generalized Fitting
subgroup, nontrivial fusion, every four-element fused core intersection,
and the full involution-centralizer order. This is the concrete witness
consumed by the abstract two-type comparison; no recognition is assumed.

Source: Aschbacher, *Sporadic Groups* (1994), Hypothesis 45.1 and the
definition of type U₄(3), printed pp.242 and 244.
-/

public section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.SourceType
open Theory.GroupTheory.Recognition.UnitaryFourThree

/-- The actual matrix group satisfies the original, unchanged type definition. -/
theorem native_isType : IsType standardInvolution where
  toCentralizerHypothesis := native_centralizerHypothesis
  intersection_card := native_intersection_card
  centralizer_card := native_centralizer_card

/-- The existence input for comparison with an arbitrary group of the same type. -/
theorem exists_native_isType : ∃ z : Carrier 4, IsType z :=
  ⟨standardInvolution,native_isType⟩

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.SourceType
