module

public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_6

/-!
This internal module proves multiplication closure for the subgroup `K₁` from
GLS3 Theorem 2.1.8.  For the twisted defect `d(g) = g⁻¹ σ(g)`, one has
`d(ab) = b⁻¹ d(a) b d(b)`.  Since `d(a)` lies in the central subgroup `Z`,
the conjugation disappears and `d(ab) = d(a)d(b)`, which belongs to `Z` by
subgroup multiplication closure.
-/

universe u

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_2_1_8_k1_mul_mem
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K) (Z : ClosedSubgroup K)
    (hZ : Z.toSubgroup ≤ Subgroup.center (Variety.Point K))
    {a b : Variety.Point K}
    (ha : a⁻¹ * σ.onPoints a ∈ Z.toSubgroup)
    (hb : b⁻¹ * σ.onPoints b ∈ Z.toSubgroup) :
    (a * b)⁻¹ * σ.onPoints (a * b) ∈ Z.toSubgroup := by
  have hcomm : b⁻¹ * (a⁻¹ * σ.onPoints a) =
      (a⁻¹ * σ.onPoints a) * b⁻¹ :=
    Subgroup.mem_center_iff.mp (hZ ha) b⁻¹
  have hproduct : (a * b)⁻¹ * σ.onPoints (a * b) =
      (a⁻¹ * σ.onPoints a) * (b⁻¹ * σ.onPoints b) := by
    calc
      (a * b)⁻¹ * σ.onPoints (a * b) =
          b⁻¹ * (a⁻¹ * σ.onPoints a) * σ.onPoints b := by
        rw [map_mul, mul_inv_rev]
        simp only [mul_assoc]
      _ = (a⁻¹ * σ.onPoints a) * (b⁻¹ * σ.onPoints b) := by
        rw [hcomm]
        simp only [mul_assoc]
  rw [hproduct]
  exact Z.toSubgroup.mul_mem ha hb

end Theory.AlgebraicGroup
