module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.Frame
/-!
# The eleven seed values of the degree-252 norm

Check the packed action of node 19 on each literal seed, and check the XOR of
its twenty-three stored orbit rows. The packed decoding theorem identifies
these XORs with the vector sums. In particular, the last sum uses row 253;
there is no truncation to the square frame.

Source: `Norm.Frame` and the unchanged `Degrees120252/source/density-252.json`.
No transition, inverse, generator-product or norm-membership premise is used.
-/

set_option Elab.async false
public section
open Matrix
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
open FactorAlgebras.Certificate MatrixChecks
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm
set_option maxRecDepth 8192 in
private theorem seed_actions : ∀ s : Fin 11,
    combineList c19 (entry orbitRows (23 * s.val + 0)) = entry c19 s.val := by decide +kernel
set_option maxRecDepth 8192 in
private theorem seed_sums : ∀ s : Fin 11,
    xorList (List.ofFn fun t : Fin 23 => entry orbitRows (23 * s.val + t.val)) =
      entry c19 s.val := by decide +kernel

set_option maxRecDepth 2048 in
theorem norm_seed : ∀ s : Fin 11, Matrix.vecMul (orbitRow s 0) normMatrix =
    ∑ t : Fin 23, orbitRow s t.val := by
  intro s
  change vecMul (vector (entry orbitRows (23 * s.val + 0))) (matrix c19) = _
  rw [← vector_combine c19 (by decide +kernel), seed_actions]
  funext j
  simp only [Finset.sum_apply, orbitRow, vector]
  rw [← seed_sums s, bit_xorList, List.map_ofFn, List.sum_ofFn]
  rfl
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm
