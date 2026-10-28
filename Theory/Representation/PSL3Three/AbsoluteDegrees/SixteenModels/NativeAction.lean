module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Transport
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Correctness
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

/-!
# The native degree-sixteen action

`actionsExist` combines the complete native edge table with the proved
correctness of packed binary-polynomial arithmetic. Identity normalization and
the two right-generator edge families give the full homomorphism law because
the native matrices generate SL₃(3). Coefficient evaluation and the canonical
SL₃(3)–PSL₃(3) isomorphism then give the action of the literal projective quotient,
with both prescribed generator matrices, over every field of characteristic two
and every parameter satisfying `t⁴=t+1`. These transport steps are proved in
`Transport`; no presentation or model equivalence is assumed.

The ATLAS data and attribution are in `SixteenModels.Data`. The consumer is the
degree-sixteen construction underlying GM02 Proposition 4.2, manuscript pp.9–10.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction
universe v

theorem actionsExist_of_packed (h : Packed.MultiplicationCorrect) (E : Packed.Certificate) :
    ActionsExist.{v} := actionsExist_of_edgeTable (E.toEdgeTable h)

/-- The checked ATLAS matrices define a genuine marked action of the native
projective group over every requested field universe. -/
theorem actionsExist : ActionsExist.{v} :=
  actionsExist_of_packed Packed.multiplicationCorrect Packed.Table.certificate

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction
