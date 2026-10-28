module

public import Theory.AlgebraicGroup.Bor1.DifferentialSurjective
public import Theory.AlgebraicGroup.Bor1.ExactKernelClosedImageProjection
public import Theory.AlgebraicGroup.Bor1.TangentDimension
public import Theory.AlgebraicGroup.Dimension.Fiber

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped Cardinal

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

set_option linter.style.haveILetI false in
/-- The exact-kernel representation supplied by Bor1 yields a point-surjective
closed-image projection whose identity differential is also surjective. -/
public theorem ExactKernelDifferentialRationalRepresentation.closedImageProjection_exactTangentKernel_surjective_exists
    (H : ClosedSubgroup G)
    (P : ExactKernelDifferentialRationalRepresentation H) :
    let Q := P.morphism.imageClosedSubgroup
    letI : AlgebraicGroup Q.carrierVariety := Q.carrierAlgebraicGroup
    ∃ pi : AlgebraicGroup.Morphism G Q.carrierVariety,
      Function.Surjective pi.onPoints ∧
      pi.kernel = H.toSubgroup ∧
      LinearMap.ker (identityTangentMorphismLinearMap pi) =
        LinearMap.range (identityTangentMorphismLinearMap H.inclusion) ∧
      Function.Surjective (identityTangentMorphismLinearMap pi) := by
  letI : AddCommGroup P.V := P.addCommGroup
  letI : Module k P.V := P.module
  letI : FiniteDimensional k P.V := P.finiteDimensional
  dsimp only
  let Q := P.morphism.imageClosedSubgroup
  letI : AlgebraicGroup Q.carrierVariety := Q.carrierAlgebraicGroup
  obtain ⟨pi, hsurj, hpiker, htangent⟩ :=
    P.closedImageProjection_exactTangentKernel_exists H
  have hpointKernel : P.morphism.kernel = H.toSubgroup := by
    rw [← P.pointKernel]
    ext g
    change P.morphism.onPoints g = 1 ↔ P.representation.action g = 1
    constructor
    · intro hg
      rw [← P.pointAction g, hg]
      simpa using P.pointAction (1 : Variety.Point G)
    · intro hg
      apply (glPointEquivOf k P.V P.basis).injective
      rw [P.pointAction g, hg]
      simpa using (P.pointAction (1 : Variety.Point G)).symm
  have hclosedKernel : P.morphism.kernelClosedSubgroup = H := by
    apply SetLike.coe_injective
    change (P.morphism.kernel : Set (Variety.Point G)) =
      (H.toSubgroup : Set (Variety.Point G))
    rw [hpointKernel]
  have hdimCard : Variety.dimension G =
      Variety.dimension H.carrierVariety +
        Variety.dimension Q.carrierVariety := by
    simpa [hclosedKernel] using morphism_dimension_eq_kernel_add_image P.morphism
  have hdimNat := congrArg Cardinal.toNat hdimCard
  have hHfin : Variety.dimension H.carrierVariety < ℵ₀ :=
    variety_dimension_lt_aleph0 H.carrierVariety
  have hQfin : Variety.dimension Q.carrierVariety < ℵ₀ :=
    variety_dimension_lt_aleph0 Q.carrierVariety
  rw [Cardinal.toNat_add hHfin hQfin] at hdimNat
  have hkerFinrank : Module.finrank k
      (LinearMap.ker (identityTangentMorphismLinearMap pi)) =
        Module.finrank k (IdentityPointDerivation H.carrierVariety) := by
    rw [htangent]
    exact LinearMap.finrank_range_of_inj
      (identityTangentMorphismLinearMap_inclusion_injective H)
  have horbitDim : Module.finrank k (IdentityPointDerivation H.carrierVariety) +
      Module.finrank k (IdentityPointDerivation Q.carrierVariety) =
        Module.finrank k (IdentityPointDerivation G) := by
    rw [identityPointDerivation_finrank_eq_dimension,
      identityPointDerivation_finrank_eq_dimension,
      identityPointDerivation_finrank_eq_dimension]
    exact hdimNat.symm
  have hdifferential :
      Function.Surjective (identityTangentMorphismLinearMap pi) := by
    apply identityTangentMorphismLinearMap_surjective_of_finrank_add_eq pi
    rw [hkerFinrank]
    exact horbitDim
  exact ⟨pi, hsurj, hpiker, htangent, hdifferential⟩

end Theory.AlgebraicGroup.Bor1
