module

public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_6

/-!
This internal module isolates inverse closure for the subgroup `K₁` from
GLS3, Theorem 2.1.8. Its conclusion is the original `Subgroup.inv_mem'`
obligation, with centrality of `Z` kept explicit. If
`z = a⁻¹ * σ(a)` is central, then `a * σ(a)⁻¹ = a * z⁻¹ * a⁻¹ = z⁻¹`;
inverse closure of `Z` therefore gives the result.
-/

universe u

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_2_1_8_k1_inv_mem
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K) (Z : ClosedSubgroup K)
    (hZ : Z.toSubgroup ≤ Subgroup.center (Variety.Point K))
    {a : Variety.Point K}
    (ha : a⁻¹ * σ.onPoints a ∈ Z.toSubgroup) :
    a⁻¹⁻¹ * σ.onPoints a⁻¹ ∈ Z.toSubgroup := by
  have hzCenter : a⁻¹ * σ.onPoints a ∈
      Subgroup.center (Variety.Point K) := hZ ha
  have hzInvCenter : (a⁻¹ * σ.onPoints a)⁻¹ ∈
      Subgroup.center (Variety.Point K) :=
    (Subgroup.center (Variety.Point K)).inv_mem hzCenter
  have hcomm : a * (a⁻¹ * σ.onPoints a)⁻¹ =
      (a⁻¹ * σ.onPoints a)⁻¹ * a :=
    Subgroup.mem_center_iff.mp hzInvCenter a
  have hsigmaInv : (σ.onPoints a)⁻¹ =
      (a⁻¹ * σ.onPoints a)⁻¹ * a⁻¹ := by
    simp [mul_inv_rev]
  have htarget : a⁻¹⁻¹ * σ.onPoints a⁻¹ =
      (a⁻¹ * σ.onPoints a)⁻¹ := by
    rw [σ.onPoints.map_inv, inv_inv, hsigmaInv, ← mul_assoc, hcomm]
    simp
  rw [htarget]
  exact Z.toSubgroup.inv_mem ha

end Theory.AlgebraicGroup
