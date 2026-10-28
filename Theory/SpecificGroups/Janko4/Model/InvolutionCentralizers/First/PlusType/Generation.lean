module

public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.PlusType.Quadratic

/-!
# Generation by the six actual hyperbolic pairs

Twelve short binary identities express each original quotient generator in
terms of the proposed hyperbolic vectors. Their lifts therefore generate the
whole quotient by the marked involution. The square of the first pair's
product is that involution, so the lifts generate the actual normal closure.
The kernel checks are on the twelve-dimensional binary space, using the
proved quotient isomorphism rather than matrix recomputation.

Source: the plus-type core in Aschbacher–Smith 16.1.5(9), printed p.1172,
and GLS3 Table 5.3i. This discharges generation for the central-product
recognition; the exact dihedral product kernel remains a separate step.
-/

open Subgroup
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreCentralizerData NormalClosureControl.IntrinsicCenter OuterImageComparison
open Janko4.Cardinality.KernelCount

namespace Janko4.InvolutionCentralizers.First.PlusType

private def pairIndex (i : Fin 12) : Fin 6 := ⟨i.val / 2, by omega⟩
private def pairSide (i : Fin 12) : Bool := i.val % 2 == 1
private def expansionMask : Fin 12 → ℕ :=
  ![3825, 3824, 3828, 3833, 3826, 2287, 1550, 45, 3923, 3004, 4087, 2234]

/-- These are identities in the binary twelve-space, checked by the kernel. -/
private theorem expansion_certificate (i : Fin 12) :
    binaryProduct (fun j => fieldVector (hyperbolicVector (pairIndex j) (pairSide j)))
      (maskBits (expansionMask i)) = vectorBasis i.succ := by
  revert i
  decide +kernel

private def expansionWord (i : Fin 12) : localNormalClosure :=
  binaryProduct (fun j => hyperbolicLift (pairIndex j) (pairSide j))
    (maskBits (expansionMask i))

private theorem expansion_projection (i : Fin 12) :
    projection (expansionWord i) = quotientBasis i.succ := by
  apply coordinates.injective
  calc
    coordinates (projection (expansionWord i)) =
        binaryProduct (fun j => coordinates (projection (hyperbolicLift (pairIndex j) (pairSide j))))
          (maskBits (expansionMask i)) :=
      map_binaryProduct (coordinates.toMonoidHom.comp projection) _ _
    _ = binaryProduct (fun j => fieldVector (hyperbolicVector (pairIndex j) (pairSide j)))
          (maskBits (expansionMask i)) := by simp_rw [hyperbolicLift_coordinates]
    _ = vectorBasis i.succ := expansion_certificate i
    _ = coordinates (quotientBasis i.succ) := (coordinates_respectsBasis i.succ).symm

private theorem mem_of_projection_eq (H : Subgroup localNormalClosure)
    (ht : centralWord ∈ H) (x y : localNormalClosure) (hy : y ∈ H)
    (h : projection x = projection y) : x ∈ H := by
  have hz : y⁻¹ * x ∈ centralPowers := by
    apply (QuotientGroup.eq_one_iff _).mp
    change projection (y⁻¹ * x) = 1
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have hp : centralPowers ≤ H := zpowers_le.mpr ht
  simpa only [mul_inv_cancel_left] using H.mul_mem hy (hp hz)

/-- The twelve explicit hyperbolic lifts generate the actual seed normal closure. -/
public theorem hyperbolicLift_generate :
    closure (Set.range (fun p : Fin 6 × Bool => hyperbolicLift p.1 p.2)) = ⊤ := by
  let H := closure (Set.range (fun p : Fin 6 × Bool => hyperbolicLift p.1 p.2))
  have hmem (i : Fin 6) (b : Bool) : hyperbolicLift i b ∈ H :=
    subset_closure ⟨(i, b), rfl⟩
  have hz : centralWord ∈ H := by
    rw [← hyperbolicLift_product_square 0]
    exact H.pow_mem (H.mul_mem (hmem 0 false) (hmem 0 true)) 2
  change H = ⊤
  apply top_unique
  rw [← basisElement_generate]
  apply (closure_le H).mpr
  rintro x ⟨i, rfl⟩
  refine Fin.cases hz (fun j => ?_) i
  apply mem_of_projection_eq H hz (basisElement j.succ) (expansionWord j)
  · exact binaryProduct_mem _ _ H (fun k => hmem (pairIndex k) (pairSide k))
  · exact (expansion_projection j).symm

end Janko4.InvolutionCentralizers.First.PlusType
