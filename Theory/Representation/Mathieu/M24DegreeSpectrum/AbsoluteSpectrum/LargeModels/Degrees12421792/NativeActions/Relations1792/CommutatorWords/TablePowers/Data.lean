module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data.Three
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data.ThreeSquare
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data.ThreeCube
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data.ThreeSixth
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data.Four
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data.FourSquare
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data.FourFourth
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data.Identity

/-!
# Shared literal inputs to the two commutator power chains

The complete input comparisons identify `three` and `four` with the fixed
candidate matrices in `CommutatorWords.Data`. Intermediate names label proposed
tables only; the independent product certificates must establish their powers.
The identity comparison below includes every diagonal row.

Source: ATLAS M24G1-P1, positive words 3 and 4; see `source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data
open Arithmetic

set_option maxRecDepth 8192 in
private theorem identityRows_original :
    identityRows.flatten = List.ofFn (fun i : Fin 1792 => 2 ^ i.val) := by
  decide +kernel

private theorem decode_diagonal (n : Nat) :
    decodeRows n (List.ofFn (fun i : Fin n => 2 ^ i.val)) = 1 := by
  ext i j
  simp [decodeRows, Thompson.BinaryMatrix.bit, Nat.testBit_two_pow,
    Matrix.one_apply, Fin.ext_iff]

/-- The closing product checks target the entire identity matrix. -/
theorem identity_eq_one : identity = 1 := by
  rw [identity, identityRows_original]
  exact decode_diagonal 1792

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.Data
