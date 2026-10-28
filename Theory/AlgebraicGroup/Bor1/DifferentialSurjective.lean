module

public import Theory.AlgebraicGroup.Bor1.Differential

universe u

set_option linter.unusedSectionVars false

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-! The finite-dimensional rank-nullity endpoint used to formulate
Bor1 separability of an orbit map. -/

public theorem identityTangentMorphismLinearMap_surjective_of_finrank_add_eq
    {H K : Variety k} [AlgebraicGroup H] [AlgebraicGroup K]
    (f : AlgebraicGroup.Morphism H K)
    (hdim : Module.finrank k
        (LinearMap.ker (identityTangentMorphismLinearMap f)) +
        Module.finrank k (IdentityPointDerivation K) =
        Module.finrank k (IdentityPointDerivation H)) :
    Function.Surjective (identityTangentMorphismLinearMap f) := by
  let d := identityTangentMorphismLinearMap f
  have hrank := LinearMap.finrank_range_add_finrank_ker d
  have hdim' : Module.finrank k (IdentityPointDerivation K) +
      Module.finrank k (LinearMap.ker d) =
      Module.finrank k (IdentityPointDerivation H) := by
    simpa [Nat.add_comm] using hdim
  have hrange : Module.finrank k (LinearMap.range d) =
      Module.finrank k (IdentityPointDerivation K) := by
    apply Nat.add_right_cancel
    exact hrank.trans hdim'.symm
  have htop : LinearMap.range d =
      (⊤ : Submodule k (IdentityPointDerivation K)) := by
    apply Submodule.eq_top_of_finrank_eq
    exact hrange
  exact LinearMap.range_eq_top.mp htop

public theorem identityTangentMorphismLinearMap_exact_kernel_and_surjective_of_finrank_eq
    {G I : Variety k} [AlgebraicGroup G] [AlgebraicGroup I]
    (H : ClosedSubgroup G) (φ : AlgebraicGroup.Morphism G I)
    (hφ : H.toSubgroup ≤ φ.kernel)
    (hdim : Module.finrank k
        (LinearMap.ker (identityTangentMorphismLinearMap φ)) =
        Module.finrank k (IdentityPointDerivation H.carrierVariety))
    (horbitDim : Module.finrank k (IdentityPointDerivation H.carrierVariety) +
        Module.finrank k (IdentityPointDerivation I) =
        Module.finrank k (IdentityPointDerivation G)) :
    LinearMap.ker (identityTangentMorphismLinearMap φ) =
        LinearMap.range (identityTangentMorphismLinearMap H.inclusion) ∧
      Function.Surjective (identityTangentMorphismLinearMap φ) := by
  have hker := identityTangentMorphismLinearMap_ker_eq_range_inclusion_of_finrank_eq
    H φ hφ hdim
  have hdim' : Module.finrank k
      (LinearMap.ker (identityTangentMorphismLinearMap φ)) +
      Module.finrank k (IdentityPointDerivation I) =
      Module.finrank k (IdentityPointDerivation G) := by
    rw [hdim]
    exact horbitDim
  exact ⟨hker,
    identityTangentMorphismLinearMap_surjective_of_finrank_add_eq φ hdim'⟩

end Theory.AlgebraicGroup.Bor1
