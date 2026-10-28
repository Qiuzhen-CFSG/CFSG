module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.KernelCompletion.Data

/-!
# The exact numerical obligations

Each Boolean predicate checks one row of a matrix identity. The two products
are B*A and (B*A)*B. The sum identifies the literal algebra element, and the
completion adds the fixed outer product. All predicates are checked in small
ranges, and `KernelCompletion` applies the soundness lemmas to those checks.
Source conventions: `../../source/README.md` and `../source/Generate.py`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.KernelCompletion.Checks
open Data

def baCheck (i : ℕ) : Bool :=
  packedMul Data1242.secondRows[i]! Data1242.firstRows.toList 0 == baRows[i]!

def babCheck (i : ℕ) : Bool :=
  packedMul baRows[i]! Data1242.secondRows.toList 0 == babRows[i]!

def elementCheck (i : ℕ) : Bool :=
  (2 ^ i ^^^ Data1242.firstRows[i]! ^^^ Data1242.secondRows[i]! ^^^ babRows[i]!) == elementRows[i]!

def completionCheck (i : ℕ) : Bool :=
  (elementRows[i]! ^^^ (if columnPacked.testBit i then rowPacked else 0)) == completedRows[i]!

def inverseCheck (i : ℕ) : Bool :=
  packedMul inverseRows[i]! completedRows.toList 0 == 2 ^ i

def columnCheck (i : ℕ) : Bool :=
  packedDot elementRows[i]! columnPacked 1242 == 0

set_option maxRecDepth 8192 in
theorem first_size : Data1242.firstRows.size = 1242 := by decide +kernel

set_option maxRecDepth 8192 in
theorem second_size : Data1242.secondRows.size = 1242 := by decide +kernel

set_option maxRecDepth 8192 in
theorem element_size : elementRows.size = 1242 := by decide +kernel

set_option maxRecDepth 8192 in
theorem completed_size : completedRows.size = 1242 := by decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.KernelCompletion.Checks
