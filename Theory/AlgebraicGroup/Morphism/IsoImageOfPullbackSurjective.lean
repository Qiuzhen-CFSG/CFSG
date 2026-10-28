module

public import Theory.AlgebraicGroup.Morphism.ClosedEmbedding
public import Theory.AlgebraicGroup.Variety.InjectiveOfPullbackSurjective

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A morphism with surjective coordinate pullback is an isomorphism onto its
closed image. -/
public theorem Morphism.iso_imageClosedSubgroup_of_pullbackRingHom_surjective
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hpull : Function.Surjective f.toVariety.pullbackRingHom) :
    let I := f.imageClosedSubgroup
    letI : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
    ∃ e : AlgebraicGroup.Iso G I.carrierVariety,
      e.hom = f.codRestrictClosedSubgroup I (fun y => ⟨y, rfl⟩) := by
  dsimp
  have hinjective : Function.Injective f.onPoints :=
    f.toVariety.injective_of_pullbackRingHom_surjective hpull
  apply f.iso_imageClosedSubgroup_of_coordinate_preimage hinjective
  intro c
  obtain ⟨q, hq⟩ := hpull
    (Variety.PolynomialFunction.ofPolynomial G (MvPolynomial.X c))
  exact ⟨q, hq⟩

end Theory.AlgebraicGroup
