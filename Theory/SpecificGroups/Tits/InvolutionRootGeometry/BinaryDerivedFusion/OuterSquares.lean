module
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.BinaryDerivedFusion.Reduction
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.BinaryDerivedFusion.OuterSquares.Certificates
-- Intentional internal use of the existing simple/root-word comparisons.
-- This does not widen their public boundary or alter the realization.
import all Theory.SpecificGroups.ReeF4.DerivedTits.Realization.TransportComparison

/-!
# Nonidentity squares in the binary Ree outer coset

The actual simple-root matrix comparison carries the outer prefix and the
marked Atlas Sylow word to the binary word checked in `Certificates`.
Scalar extension is injective, so a nonidentity binary square gives a
nonidentity square in the literal fixed Ree group. This discharges exactly
the finite-check premise of `square_one_mem_derived_of_check`.

Source: Parrott (1972), §5, printed p.683; GLS3 Table 2.4 and 2.4.5(d).
The full Ree carrier and its embedded derived Tits subgroup are kept distinct.
-/

public section
noncomputable section
namespace Tits.InvolutionRootGeometry.BinaryDerivedFusion
open ReeF4 ReeF4.DerivedTits.Realization
open ReeF4.DerivedTits.Realization.TransportComparison.Products
open OuterSquares

private theorem compare_binaryWord (n : Fin 2048)
    (e : Theory.AlgebraicGroup.F4Chevalley.BasisIndex ≃ Fin 52)
    (he : SimpleMatrixComparison e) :
    renumber e (toSplitGroup 0 (fixedU 0 *
      ExceptionalParabolics.FullRee.atlasEmbedding (atlas1600SylowTwoNormalForm n))).val =
      extendScalars (binaryWord n.val) := by
  rw [atlas1600SylowTwoNormalForm_eq]
  simp only [binaryWord, map_mul, map_pow, fixedU_matrix,
    ExceptionalParabolics.FullRee.atlasEmbedding_generator_matrix,
    Subgroup.coe_mul, Subgroup.coe_pow, compare_relative e he, compare_generator e he]

/-- The literal binary Ree outer normal forms never have square one. -/
theorem outer_normalForm_square_ne_one (n : Fin 2048) :
    (fixedU 0 * Tits.ExceptionalParabolics.FullRee.atlasEmbedding
      (Tits.atlas1600SylowTwoNormalForm n)) ^ 2 ≠ 1 := by
  intro h
  obtain ⟨e, he⟩ := exists_simpleMatrixComparison
  have hs := congrArg (fun x : Model 0 => renumber e (toSplitGroup 0 x).val) h
  simp only [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one,
    compare_binaryWord n e he] at hs
  apply binaryWord_square_ne_one n
  apply Units.ext
  apply Matrix.map_injective binaryScalar.injective
  change (extendScalars ((binaryWord n.val)^2)).val = (extendScalars 1).val
  rw [map_pow, map_one]
  exact congrArg Units.val hs

end Tits.InvolutionRootGeometry.BinaryDerivedFusion
