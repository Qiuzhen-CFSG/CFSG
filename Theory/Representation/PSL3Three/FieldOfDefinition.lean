module

public import Theory.Representation.PSL3Three.NativeFieldCalculation.Models

/-!
# The degree-sixteen field obstruction for PSL₃(3)

Every faithful absolutely irreducible degree-sixteen representation of the
literal projective matrix group in characteristic two has coefficient field
larger than the binary prime field. The native calculation constructs seven
inequivalent simple modules and proves that they exhaust the odd-class bound.
Frobenius and the four binary-power conjugacy classes then force a nonbinary
trace on every degree-sixteen simple. Scalar extension of a representation
over a two-element field would have only binary traces, a contradiction.

`degreeSixteenFieldObstruction` supplies the exact contract in
`SmallDegreeDescent`, with all construction and class-count inputs discharged.
Its application `binary_degree_twelve` uses the independently proved absolute
degree window on the Schur endomorphism field; the input binary representation
need only be irreducible. Both results retain arbitrary carrier universes.

Source context: Guralnick--Malle, *Classification of 2F-modules I*, Proposition
4.2, manuscript pp.9–10. This proves the field restriction used in its
small-degree reduction, without assuming a character table or asserting the
full proposition's offender conclusions. The exact minimal field is not needed.
-/

namespace Representation.PSL3Three.FieldOfDefinition
universe v

/-- An absolute degree-sixteen representation of the native PSL₃(3) cannot be
defined over a field of cardinality two. No model or trace premise remains. -/
public theorem degreeSixteenFieldObstruction : DegreeSixteenFieldObstruction.{v} :=
  NativeFieldCalculation.degreeSixteenFieldObstruction

/-- Discharge both native calculation premises of the actual Schur-field
descent consumer, without assuming absolute irreducibility over the binary field. -/
public theorem binary_degree_twelve
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) Matrix.PSL3Three.PSL W) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) W ≤ 18) :
    Module.finrank (ZMod 2) W = 12 :=
  binary_degree_twelve_of_absolute_calculations AbsoluteDegrees.absoluteDegreeWindow
    degreeSixteenFieldObstruction σ hf hd

end Representation.PSL3Three.FieldOfDefinition
