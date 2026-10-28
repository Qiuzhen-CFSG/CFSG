module
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Matrices.Rows
/-!
# Literal packed identity

The identity is stored as the already supplied `uv00Rows` vector. Kernel
reduction checks its 112 entries once. Rewriting to this literal vector avoids
repeated construction of `Vector.ofFn` inside the normal-form product checks.
See `Rows` for source attribution.
-/

public section
namespace Janko4.Simplicity.ThreeLocalCertificates
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000 in
theorem packedOne_eq_uv00Rows : packedOne = uv00Rows := by
  have h : ∀ i : Fin 112, 2 ^ i.val = uv00Rows.get i := by decide +kernel
  apply Vector.ext
  intro i hi
  change packedOne.get ⟨i, hi⟩ = uv00Rows.get ⟨i, hi⟩
  rw [packedOne, get_ofFn]
  exact h ⟨i, hi⟩
end Janko4.Simplicity.ThreeLocalCertificates
