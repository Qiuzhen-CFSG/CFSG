module
public import Theory.SpecificGroups.GL2.NoncommutativeCentralizer

/-!
# The exact scalar center of a noncommutative GL2 subgroup

For any noncommutative subgroup D of GL2 over a field, the image of its
center under the actual inclusion is exactly D intersected with the range
of the scalar homomorphism from field units. No finite-field, parity,
determinant, or irreducibility assumption is required.

An element central in D centralizes the actual ambient subset D, so the
proved noncommutative-centralizer theorem makes it scalar. Conversely,
a scalar matrix lying in D commutes with every element of D and therefore
belongs to its center. Both directions preserve the original subgroup
and scalar map; no matrix commutant argument is repeated.

This supplies the precise central kernel in the linear and unitary
model comparisons of ABG II.2 Lemma 1(v) and II.3 Proposition 3, article
page 26. Determinant-level specializations are separate consumers.
-/

namespace Matrix.GeneralLinearGroup

public theorem center_map_eq_inf_scalar_of_noncommutative
    {F : Type*} [Field F] (D : Subgroup (GL (Fin 2) F)) (hD : ¬ IsMulCommutative D) :
    (Subgroup.center D).map D.subtype =
      D ⊓ (scalar (Fin 2) : Fˣ →* GL (Fin 2) F).range := by
  apply le_antisymm
  · rintro x ⟨z, hz, rfl⟩
    refine ⟨z.property, centralizer_le_scalar_of_noncommutative D hD ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨y, hy⟩)
  · rintro x ⟨hx, u, hu⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    change y.val * x = x * y.val
    rw [← hu]
    exact (scalar_commute u y.val).symm

end Matrix.GeneralLinearGroup

