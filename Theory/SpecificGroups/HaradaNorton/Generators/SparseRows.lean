module

public import Theory.SpecificGroups.HaradaNorton.MatrixData

/-!
# Sparse row certificates for the Harada–Norton generators

A certified support restricts a matrix product to its nonzero summands. This
keeps the kernel checks of the ATLAS matrices small, especially for their many
singleton rows. Source data and attribution: `../MatrixSources.md`.
-/

namespace HaradaNorton.GeneratorCertificates

/-- Restrict a product row to a certified support of its left factor. -/
public theorem sparse_mul_row (A B : Matrix133) (i : Fin 133) (s : Finset (Fin 133))
    (h : ∀ k, k ∉ s → A i k = 0) (j : Fin 133) :
    (A * B) i j = ∑ k ∈ s, A i k * B k j := by
  rw [Matrix.mul_apply]
  exact (Finset.sum_subset (Finset.subset_univ s)
    (fun k _ hk => by rw [h k hk, zero_mul])).symm

end HaradaNorton.GeneratorCertificates
