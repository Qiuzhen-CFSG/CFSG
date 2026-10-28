module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.CycleSimplicity.Certificate.Checked

/-!
# Density of the binary cycle quotient matrices

The checked rank-one operator and its two spanning word orbits generate all
matrix units. Coefficient casting preserves this conclusion over any field
of characteristic two. The geometric realization identifies these matrices
with the actual incidence-cycle quotient of PSL₃(3).
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.CycleSimplicity.Certificate
open Thompson.BinaryMatrix CycleCertificate

attribute [local irreducible] values leftIndex rightIndex column row columns rows
  columnInverse rowInverse

/-- The two explicit binary quotient actors generate the full matrix algebra. -/
theorem algebra_eq_top
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 26) (Fin 26) (ZMod 2)))
    (h : ∀ a, Data.actorMatrix a ∈ Q) : Q = ⊤ := by
  have hcr : Matrix.vecMulVec (fun i : Fin 26 => bit column i.val)
      (fun i : Fin 26 => bit row i.val) ∈ Q := by
    rw [← rank_one]
    exact value_mem Q h 56 (by decide)
  have hL (i : Fin 26) : decode 26 values[leftIndex i]! ∈ Q :=
    value_mem Q h _ (leftIndex_lt i)
  have hR (i : Fin 26) : decode 26 values[rightIndex i]! ∈ Q :=
    value_mem Q h _ (rightIndex_lt i)
  exact density_of_rank_one Q (fun i : Fin 26 => bit column i.val)
    (fun i : Fin 26 => bit row i.val) hcr
    (fun i => decode 26 values[leftIndex i]!)
    (fun i => decode 26 values[rightIndex i]!) hL hR
    (decode 26 columns) (decode 26 columnInverse) (decode 26 rows) (decode 26 rowInverse)
    columns_inverse rows_inverse left_action right_action

/-- The same matrices generate all endomorphisms over every characteristic-two field. -/
theorem algebra_eq_top_charTwo (F : Type*) [Field F] [CharP F 2]
    (Q : Subalgebra F (Matrix (Fin 26) (Fin 26) F))
    (h : ∀ a, castMatrix F (Data.actorMatrix a) ∈ Q) : Q = ⊤ :=
  density_cast F Data.actorMatrix algebra_eq_top Q h

end Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.CycleSimplicity.Certificate
