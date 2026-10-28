module

public import Theory.AlgebraicGroup.Bor1.WeightSpacePermutation
public import Theory.AlgebraicGroup.Bor1.WeightDecompositionCentralizer

universe u v w

namespace Theory.AlgebraicGroup.Bor1

variable {k : Type u} [Field k]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- Bor1 §5.6's point-kernel argument on the actual common-weight span.
Once a distinguished subspace inside one weight block has stabilizer `N`,
conjugation on the block-diagonal endomorphisms has kernel exactly `N`. -/
public theorem Representation.commonWeightBlock_conjRepresentation_ker_eq_of_lineStabilizer
    [FiniteDimensional k V]
    (ρ : Representation k Γ V) (N : Subgroup Γ) [N.Normal]
    (τ : Γ →* LinearMap.GeneralLinearGroup k
      (Representation.commonWeightSpan ρ N))
    (hτ : ∀ g x,
      ((((τ g : LinearMap.GeneralLinearGroup k
        (Representation.commonWeightSpan ρ N)) : Module.End k
          (Representation.commonWeightSpan ρ N)) x :
            Representation.commonWeightSpan ρ N) : V) =
        (ρ g : Module.End k V) (x : V))
    (D : Submodule k (Representation.commonWeightSpan ρ N))
    (χD : Representation.commonWeightIndex ρ N)
    (hD : D ≤ Representation.commonWeightBlock ρ N χD)
    (hStabilizer : ∀ g : Γ,
      Submodule.map
        (τ g : Module.End k (Representation.commonWeightSpan ρ N)) D = D ↔
        g ∈ N) :
    (blockDiagonalEnd_conjRepresentation
      (Representation.commonWeightBlock ρ N) τ
      (Representation.normalCommonWeightPermutation ρ N)
      (Representation.commonWeightBlock_map_of_restriction ρ N τ hτ)).ker = N := by
  apply blockDiagonalEnd_conjRepresentation_ker_eq_of_lineStabilizer
    (Representation.commonWeightBlock ρ N)
    (Representation.commonWeightBlock_iSupIndep ρ N)
    (Representation.commonWeightBlock_iSup_eq_top ρ N)
    τ (Representation.normalCommonWeightPermutation ρ N)
    (Representation.commonWeightBlock_map_of_restriction ρ N τ hτ)
    D χD hD N hStabilizer
  intro n
  exact Representation.commonWeightBlock_scalar_of_mem_of_restriction
    ρ N τ hτ n

end Theory.AlgebraicGroup.Bor1
