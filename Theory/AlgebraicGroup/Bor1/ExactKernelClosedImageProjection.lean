module

public import Theory.AlgebraicGroup.Bor1.ExactKernelTangentRepresentation
public import Theory.AlgebraicGroup.Morphism.ClosedImage

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

set_option linter.style.haveILetI false in
/-- Restricting an exact-kernel representation to its closed image preserves
both its prescribed point kernel and its prescribed tangent kernel. -/
public theorem ExactKernelDifferentialRationalRepresentation.closedImageProjection_exactTangentKernel_exists
    (H : ClosedSubgroup G)
    (P : ExactKernelDifferentialRationalRepresentation H) :
    let Q := P.morphism.imageClosedSubgroup
    letI : AlgebraicGroup Q.carrierVariety := Q.carrierAlgebraicGroup
    ∃ pi : AlgebraicGroup.Morphism G Q.carrierVariety,
      Function.Surjective pi.onPoints ∧
      pi.kernel = H.toSubgroup ∧
      LinearMap.ker (identityTangentMorphismLinearMap pi) =
        LinearMap.range (identityTangentMorphismLinearMap H.inclusion) := by
  letI : AddCommGroup P.V := P.addCommGroup
  letI : Module k P.V := P.module
  letI : FiniteDimensional k P.V := P.finiteDimensional
  dsimp only
  let Q := P.morphism.imageClosedSubgroup
  letI : AlgebraicGroup Q.carrierVariety := Q.carrierAlgebraicGroup
  obtain ⟨pi, hsurj, hpiker, hcompPoint⟩ :=
    P.morphism.closedImageProjection_exists
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
  have hcomp : Q.inclusion.comp pi = P.morphism := by
    apply AlgebraicGroup.Morphism.ext
    funext g
    exact hcompPoint g
  refine ⟨pi, hsurj, hpiker.trans hpointKernel, ?_⟩
  rw [← P.tangentKernel H]
  ext D
  simp only [LinearMap.mem_ker]
  constructor
  · intro hD
    rw [← hcomp]
    rw [identityTangentMorphismLinearMap_comp]
    simp [hD]
  · intro hD
    apply identityTangentMorphismLinearMap_inclusion_injective Q
    change identityTangentMorphismLinearMap Q.inclusion
        (identityTangentMorphismLinearMap pi D) =
      identityTangentMorphismLinearMap Q.inclusion 0
    rw [← LinearMap.comp_apply, ← identityTangentMorphismLinearMap_comp]
    rw [hcomp, hD]
    rfl

end Theory.AlgebraicGroup.Bor1
