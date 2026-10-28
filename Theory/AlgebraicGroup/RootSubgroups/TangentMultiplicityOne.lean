module

public import Theory.AlgebraicGroup.RootSubgroups.Finite
public import Theory.AlgebraicGroup.RootSubgroups.MultiplicityOne

/-!
# From tangent multiplicity to root-subgroup multiplicity

This module isolates the formal passage from two geometric facts about the
identity-tangent representation to the operational multiplicity-one property
for torus root subgroups.  If the inverse-character weight space is a line,
then the nonzero tangents of two root parametrizations are proportional.  If
all higher powers of that inverse character are absent, tangent rigidity
integrates the proportionality to equality of the ambient one-parameter
curves after scalar rescaling.

The higher-weight hypothesis is essential in positive characteristic, where a
Frobenius term can have zero tangent.  Thus the theorem keeps separate the two
characteristic-uniform geometric inputs needed for root-subgroup uniqueness
in GLS3, Theorem 1.9.5(b), and uses no conclusion of that theorem.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A one-dimensional inverse-character tangent space and absence of higher
inverse-character weights imply operational root-weight multiplicity one. -/
public theorem rootWeightSpaceMultiplicityOne_of_tangent_finrank_eq_one
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (chi : TorusWeight T)
    (hfinrank : Module.finrank k
      (weightSpace (identityTangentRepresentation K) T chi⁻¹) = 1)
    (higherWeights : ∀ n : Nat, 2 ≤ n →
      weightSpace (identityTangentRepresentation K) T ((chi⁻¹) ^ n) = ⊥) :
    RootWeightSpaceMultiplicityOne T chi := by
  intro X Y _hX hXchi _hY hYchi x y
  have hx := oneParameterTangent_isWeightVector T X x hXchi
  have hy := oneParameterTangent_isWeightVector T Y y hYchi
  let vx : weightSpace (identityTangentRepresentation K) T chi⁻¹ :=
    ⟨oneParameterTangent X x, hx.2⟩
  let vy : weightSpace (identityTangentRepresentation K) T chi⁻¹ :=
    ⟨oneParameterTangent Y y, hy.2⟩
  have hvy : vy ≠ 0 := by
    intro h
    exact hy.1 (congrArg Subtype.val h)
  obtain ⟨c, hcxy⟩ :=
    exists_smul_eq_of_finrank_eq_one hfinrank hvy vx
  have hcxy' : c • oneParameterTangent Y y = oneParameterTangent X x :=
    congrArg Subtype.val hcxy
  have hc : c ≠ 0 := by
    intro hc
    rw [hc, zero_smul] at hcxy'
    exact hx.1 hcxy'.symm
  refine ⟨c, hc, ?_⟩
  apply includePoint_eq_rescale_of_oneParameterTangent_eq_smul
    T X Y hXchi hYchi x y higherWeights c hc
  exact hcxy'.symm

end Theory.AlgebraicGroup
