module

public import Theory.Representation.MathieuCodeRestriction.Construction
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Orthogonality of the native Golay code

The coordinate dot product is nondegenerate and invariant under the native
Mathieu permutation action. The twelve certified rows pair to zero, so the
whole Golay space is self-orthogonal. Its dimension twelve then identifies
its orthogonal complement with itself. The even-weight core is exactly the
orthogonal complement of the constant line.

These are the bilinear-form assertions underlying the code/cocode duality
in Aschbacher–Smith, H.13.1, printed p.395 (combined manuscript of 1 March
2004). All row calculations are checked by the Lean kernel on the existing
native coordinates; no comparison with an unrelated code is assumed.
-/

@[expose] public section

open scoped BigOperators
open Sporadic.Mathieu
namespace MathieuCode

/-- The source intersection-parity pairing on the binary permutation module. -/
def dotForm : LinearMap.BilinForm (ZMod 2) Full := dotProductBilin (ZMod 2) (ZMod 2)

theorem dotForm_nondegenerate : dotForm.Nondegenerate := by
  constructor
  · intro v hv
    funext i
    simpa [dotForm, dotProductBilin, dotProduct_single] using hv (Pi.single i 1)
  · intro v hv
    funext i
    simpa [dotForm, dotProductBilin, single_dotProduct] using hv (Pi.single i 1)

private theorem dotForm_rows (i j : Fin 12) : dotForm (row i) (row j) = 0 := by
  revert i j
  decide +kernel

theorem golay_le_orthogonal : golay ≤ dotForm.orthogonal golay := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩ v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨j, rfl⟩ := hv
    exact dotForm_rows j i
  | zero => simp
  | add v w _ _ hv hw => simp [hv, hw]
  | smul c v _ hv => simp [hv]

/-- The native twelve-dimensional Golay code is its own orthogonal complement. -/
theorem golay_orthogonal_eq : dotForm.orthogonal golay = golay := by
  apply (Submodule.eq_of_le_of_finrank_eq golay_le_orthogonal ?_).symm
  rw [LinearMap.BilinForm.finrank_orthogonal dotForm_nondegenerate, finrank_golay]
  rw [BinaryPermutation.finrank_full]
  rfl

theorem dotForm_invariant (g : M24) (v w : Full) :
    dotForm (fullRepresentation g v) (fullRepresentation g w) = dotForm v w := by
  change (∑ i : Fin 24, v (g.val.symm i) * w (g.val.symm i)) = ∑ i, v i * w i
  exact Equiv.sum_comp g.val.symm (fun i => v i * w i)

theorem dotForm_symmetric : dotForm.IsSymm := by
  exact ⟨fun v w => dotProduct_comm v w⟩

theorem core_eq_orthogonal_constants :
    BinaryPermutation.core (Fin 24) = dotForm.orthogonal (BinaryPermutation.constants (Fin 24)) := by
  ext v
  constructor
  · intro hv u hu
    change (∑ i, v i) = 0 at hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    change dotForm (c • BinaryPermutation.allOne (Fin 24)) v = 0
    simp [dotForm, dotProductBilin, dotProduct, BinaryPermutation.allOne,
      hv]
  · intro hv
    have h := hv _ (Submodule.subset_span (Set.mem_singleton (BinaryPermutation.allOne (Fin 24))))
    change (∑ i, v i) = 0
    simpa [dotForm, dotProductBilin, dotProduct, BinaryPermutation.allOne] using h

end MathieuCode
