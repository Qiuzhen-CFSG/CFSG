module

public import Theory.AlgebraicGroup.Bor1.RepresentationDifferential

universe u v

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

omit [FiniteDimensional k V] in
/-- If the ordinary tangent morphism of a representing general-linear
morphism vanishes, then its coordinate representation differential vanishes. -/
public theorem rationalRepresentationDifferential_eq_zero_of_identityTangentMorphismLinearMap_eq_zero
    (ρ : RationalRepresentation G V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (D : IdentityPointDerivation G)
    (hzero : identityTangentMorphismLinearMap f D = 0) :
    rationalRepresentationDifferential ρ b f D = 0 := by
  have hcoefficient (i j : Fin (Module.finrank k V)) :
      D (rationalRepresentationMatrixCoefficient ρ b f i j) = 0 := by
    change identityTangentMorphismLinearMap f D
      (generalLinearMatrixCoordinate (Module.finrank k V) i j) = 0
    rw [hzero]
    rfl
  change (∑ i, ∑ j,
    D (rationalRepresentationMatrixCoefficient ρ b f i j) • b.end (i, j)) = 0
  simp only [hcoefficient, zero_smul, Finset.sum_const_zero]

omit [FiniteDimensional k V] in
/-- If a closed subgroup lies in a rational representation's point kernel,
the representation differential kills the image of the subgroup tangent
space. -/
public theorem rationalRepresentationDifferential_comp_inclusion_eq_zero_of_kernel_le
    (H : ClosedSubgroup G)
    (ρ : RationalRepresentation G V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V b (f.onPoints g) = ρ.action g)
    (hker : H.toSubgroup ≤ ρ.action.ker)
    (D : IdentityPointDerivation H.carrierVariety) :
    rationalRepresentationDifferential ρ b f
      (identityTangentMorphismLinearMap H.inclusion D) = 0 := by
  have hfker : H.toSubgroup ≤ f.kernel := by
    intro g hg
    change f.onPoints g = 1
    apply (glPointEquivOf k V b).injective
    rw [hf g]
    rw [show glPointEquivOf k V b (1 : Variety.Point (glVarietyOf k V)) = 1 by
      simpa using hf (1 : Variety.Point G)]
    exact hker hg
  apply rationalRepresentationDifferential_eq_zero_of_identityTangentMorphismLinearMap_eq_zero
  exact identityTangentMorphismLinearMap_comp_inclusion_eq_zero_of_kernel_le
    H f hfker D

end Theory.AlgebraicGroup.Bor1
