module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.TwelfthPower.Arithmetic

/-! Widening with a zero-skipping branch.
The low-byte test is only a performance choice: both branches are proved
equal to full radix expansion for every input. The actual consumers are
the complete W and W3 widening certificates. See `source/README.md`. -/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.TwelfthPower.SparseWidening
open Arithmetic
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders
def expandMixed (a : Nat) : Nat :=
  if a % 256 = 0 ∨ a < 256 then expandTree 6 1242 a else expand1242 a
theorem expandMixed_eq (a : Nat) : expandMixed a = Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic.expand 1242 a := by
  simp only [expandMixed, expandTree_eq, expand1242_eq, ite_self]
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.TwelfthPower.SparseWidening
