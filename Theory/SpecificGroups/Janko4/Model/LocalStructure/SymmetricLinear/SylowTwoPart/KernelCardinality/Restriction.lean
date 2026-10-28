module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality.Arithmetic
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.Filtration

/-!
# Restriction for the max4 binary-product certificate

The existing ATLAS generator and block-flag certificates show that the first 28 coordinates form an invariant block. Restricting the actual representation to this block is multiplicative.

The concrete consumer is `KernelCardinality.lean`; matrix and word sources
are the ATLAS representation and J4G1-max4W1, attributed in Model.Data and
SymmetricLinear.Model. See SylowTwoPart/source/README.md.
-/

@[expose] public section

open Matrix
namespace Janko4.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality
def restrict (M : BinaryMatrix) : SmallMatrix := M.submatrix (Fin.castAdd 84) (Fin.castAdd 84)

lemma block_separation (i : Fin 28) (j : Fin 84) :
    OrderBound.blockIndex (Fin.castAdd 84 i) < OrderBound.blockIndex (Fin.natAdd 28 j) := by
  have h₁ : ∀ i : Fin 28, OrderBound.blockIndex (Fin.castAdd 84 i) ≤ 2 := by decide +kernel
  have h₂ : ∀ j : Fin 84, 3 ≤ OrderBound.blockIndex (Fin.natAdd 28 j) := by decide +kernel
  exact lt_of_le_of_lt (h₁ i) (lt_of_lt_of_le (by decide) (h₂ j))

lemma restrict_mul (A B : BinaryMatrix)
    (hA : ∀ (i : Fin 28) (j : Fin 84), A (Fin.castAdd 84 i) (Fin.natAdd 28 j) = 0) :
    restrict (A * B) = restrict A * restrict B := by
  ext i j
  simp only [restrict, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Fin.sum_univ_add (a := 28) (b := 84)]
  simp only [hA, zero_mul, Finset.sum_const_zero, add_zero]

lemma restrict_one : restrict (1 : BinaryMatrix) = 1 := by
  ext i j
  simp [restrict, Matrix.one_apply, Fin.ext_iff]

def representation : max4Subgroup →* SmallMatrix where
  toFun g := restrict (OrderBound.representation g)
  map_one' := by rw [map_one, restrict_one]
  map_mul' g h := by
    rw [map_mul]
    exact restrict_mul _ _ (fun i j => OrderBound.representation_triangular g (block_separation i j))
end Janko4.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality
