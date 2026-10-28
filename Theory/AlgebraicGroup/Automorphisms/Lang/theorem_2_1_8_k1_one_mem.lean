module

public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_6

/-!
This internal module isolates the identity-closure obligation for the subgroup
`K₁` used in source Theorem 2.1.8.  The statement is exactly the corresponding
`Subgroup.one_mem'` field from the GLS3 construction.  The proof reduces the
twisted commutator of the identity using inversion, preservation of identity by
the point homomorphism induced by `σ`, and multiplication by identity; the
result is then `Z`'s subgroup identity.
-/

universe u

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_2_1_8_k1_one_mem
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K) (Z : ClosedSubgroup K) :
    (1 : Variety.Point K)⁻¹ * σ.onPoints 1 ∈ Z.toSubgroup := by
  rw [inv_one, σ.onPoints.map_one, mul_one]
  exact Z.toSubgroup.one_mem

end Theory.AlgebraicGroup
