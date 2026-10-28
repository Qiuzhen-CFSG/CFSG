module

public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Recovering Vector Polynomial Coefficients

If a vector-valued polynomial of degree less than `n` takes values in a
submodule at `n` distinct field elements, all its coefficient vectors lie in
that submodule. No finite-dimensionality assumption is required.

A separating linear functional would turn a coefficient outside the submodule
into a nonzero scalar coefficient while annihilating all sampled values. The
scalar Vandermonde theorem rules this out. This elementary interpolation step
is used to extract coefficient operators from the unipotent orbits of SL2
binary forms in the restricted-weight construction of Fong--Wong (1.15).
-/

namespace Submodule

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

public theorem coeff_mem_of_sum_pow_smul_mem {n : ℕ} (W : Submodule F V)
    (c : Fin n → V) (x : Fin n → F) (hx : Function.Injective x)
    (heval : ∀ i, ∑ j : Fin n, x i ^ (j : ℕ) • c j ∈ W) (j : Fin n) :
    c j ∈ W := by
  classical
  by_contra hj
  obtain ⟨f, hf, hW⟩ := W.exists_le_ker_of_notMem hj
  have hzero : (fun j => f (c j)) = 0 := by
    apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero hx
    intro i
    have h := hW (heval i)
    simpa only [LinearMap.mem_ker, map_sum, map_smul, smul_eq_mul] using h
  exact hf (congrFun hzero j)

end Submodule
