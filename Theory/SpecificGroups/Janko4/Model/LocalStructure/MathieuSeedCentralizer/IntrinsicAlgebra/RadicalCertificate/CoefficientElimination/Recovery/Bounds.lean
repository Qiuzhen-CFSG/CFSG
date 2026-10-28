module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.CoefficientElimination.RecoveryCriterion

/-!
# Indexing the finite recovery checks

Each checked block uses its own finite index type. Translation by the block's
lower endpoint identifies these checks with the corresponding original exterior
coordinates. This is the indexing step for the certificate in `source/README.md`.
-/

public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.CoefficientElimination

theorem rowChecks_of_block {b n : ℕ} (hbn : b + n ≤ 1221)
    (h : ∀ i : Fin n, RowChecks ⟨b + i.val, by omega⟩)
    (j : Fin 1221) (hlo : b ≤ j.val) (hhi : j.val < b + n) : RowChecks j := by
  have hm : j.val - b < n := by omega
  have heq : (⟨b + (j.val - b), by omega⟩ : Fin 1221) = j :=
    Fin.ext (show b + (j.val - b) = j.val by omega)
  exact heq ▸ h ⟨j.val - b, hm⟩

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.CoefficientElimination
