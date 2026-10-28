module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.RowWords
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.KernelRows
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Basic

/-!
# Square-one coordinates satisfy the packed-row test

If a literal source element squares to one, it equals its inverse. For a
kernel word followed by a lift, the inverse is the inverse lift followed by
the selected inverse factors in reverse order. Evaluating that word proves
the necessary row identity. The required matrix evaluations are explicit:
this module neither assumes nor concludes first-row faithfulness.

The factor words and rows come from the unchanged ATLAS `J4G1-max2W1`
program; attribution is preserved under `TwoCoreCentralizer/source/`.
See also `Coverage/source/README.md` and Aschbacher--Smith,
`refs/quasithin.pdf`, printed pp.64--65, A.6.1--4.
-/

public section
open scoped Matrix
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage
open Coordinates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation
open Janko4.GeneratorCertificates KernelRows

theorem firstRow_forward
    (hlift : ∀ j, sourceMatrix (sourceLift j) = decodeRows (liftRows j))
    (j : Fin 4) (m : Fin 8192) :
    firstRow (sourceElement j m) = unpackRow (forwardRow j m) := by
  change sourceMatrix (kernelProduct m * sourceLift j) 0 = _
  rw [map_mul, hlift, Matrix.mul_apply_eq_vecMul]
  have hk : sourceMatrix (kernelProduct m) 0 = unpackRow (KernelSeparation.row m.val) := by
    funext c
    exact firstRow_kernelProduct m c
  rw [hk]
  exact (unpack_packedRow _ _).symm

theorem eval_inverse_kernelProduct
    (hfactor : ∀ i, sourceMatrix (kernelFactor i)⁻¹ = decodeRows (inverseFactorRows i))
    (m : Fin 8192) :
    sourceMatrix (kernelProduct m)⁻¹ = ((inverseFactors m).map decodeRows).prod := by
  rw [kernelProduct, List.prod_inv_reverse, map_list_prod, List.map_reverse,
    List.map_map, List.map_ofFn]
  rw [inverseFactors, List.map_reverse, List.map_ofFn]
  congr 2
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  split_ifs
  · exact hfactor i
  · rw [inv_one, map_one, decode_packedOne]

theorem firstRow_backward
    (hlift : ∀ j, sourceMatrix (sourceLift j)⁻¹ = decodeRows (liftRows j))
    (hfactor : ∀ i, sourceMatrix (kernelFactor i)⁻¹ = decodeRows (inverseFactorRows i))
    (j : Fin 4) (m : Fin 8192) :
    firstRow (sourceElement j m)⁻¹ = unpackRow (backwardRow j m) := by
  change sourceMatrix (kernelProduct m * sourceLift j)⁻¹ 0 = _
  rw [mul_inv_rev, map_mul, hlift, eval_inverse_kernelProduct hfactor,
    Matrix.mul_apply_eq_vecMul]
  exact (unpack_rowWord _ _).symm

theorem rowsAgree_of_square_one
    (hlift : ∀ j, sourceMatrix (sourceLift j) = decodeRows (liftRows j))
    (hinvlift : ∀ j, sourceMatrix (sourceLift j)⁻¹ = decodeRows (liftRows j))
    (hfactor : ∀ i, sourceMatrix (kernelFactor i)⁻¹ = decodeRows (inverseFactorRows i))
    (j : Fin 4) (m : Fin 8192) (hsq : (sourceElement j m)^2 = 1) : RowsAgree j m := by
  have hi : (sourceElement j m)⁻¹ = sourceElement j m :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsq)
  unfold RowsAgree
  rw [← firstRow_forward hlift, ← firstRow_backward hinvlift hfactor, hi]

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage
