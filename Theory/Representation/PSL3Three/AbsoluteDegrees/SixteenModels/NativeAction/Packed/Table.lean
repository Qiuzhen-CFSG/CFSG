module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.Assembly
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Transport

/-!
# The complete packed native PSL₃(3) edge certificate

This constructs `Packed.Certificate` for the literal native base-three matrix
codes. All 3⁹ codes are covered; on every determinant-one code the two specified
right-generator edges hold. The image of the native identity is `Packed.one`.

The proof shares 2808 packed rows across the 5616 matrix images. Trusted kernel
checks certify every row edge and every native-code transition. The coordinate
lemmas for twelve-bit slots connect the compact numerical checks to the exact
vector equalities of `Packed.Certificate`.

Numerical source: Wilson, Nickerson and Bray, ATLAS L33G1-f16r16aB0 and
L33G1-f3r3aB0; attribution and reproducible generation are in `Table/source`.
This supplies the native action input for the degree-sixteen construction used
in GM02 Proposition 4.2. The actual action consumer below still explicitly
requires the independent `Packed.MultiplicationCorrect` theorem.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

/-- The fully checked finite numerical witness. -/
def certificate : Certificate := certificateOfChecks row_correct native_correct

theorem nonempty_certificate : Nonempty Certificate := ⟨certificate⟩

universe v

/-- Actual consumer: only packed-arithmetic correctness remains explicit. -/
theorem actionsExist (h : MultiplicationCorrect) : ActionsExist.{v} :=
  actionsExist_of_edgeTable (certificate.toEdgeTable h)

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
