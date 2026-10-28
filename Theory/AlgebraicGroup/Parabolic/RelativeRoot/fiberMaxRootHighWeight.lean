module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.borel_levi_max_root_action

/-!
# Maximal-root high weight in a relative-root fiber

This module packages the source-specific high-weight conclusion used in GLS3,
Chapter 1, Theorem 1.14.7.  For an absolute root of maximal height in the
selected relative-root fiber, the concrete Chevalley conjugation calculation
shows that every nonzero root vector spans an invariant line for the induced
Levi Borel.  The source torus acts through the inverse pulled-back root
character: the maintained representation is left conjugation `l * x * l^-1`,
while `RootWeightEquation` uses `t^-1 * x * t`.

The underlying theorem supplies root-vector nonvanishing, parameter
homogeneity, the maximal-root Borel action, and torus character compatibility.
Choosing parameter `1` therefore produces the required high-weight vector.
This result is independent of the numbered theorem and provides its final
source-level high-weight input.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

/-- A maximal-height root in a relative-root fiber supplies a high-weight
vector for the induced Levi Borel.  With the left-conjugation representation,
the weight is the inverse of the source root character pulled back to the
induced Levi torus. -/
public theorem RelativeRootFiberModule.maximalRoot_hasHighWeight
    (S : RelativeRootRepresentationSource K)
    (M : RelativeRootFiberModule S)
    (gamma : { gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root })
    (hgammaMax : ∀ eta, eta ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root →
      S.D.height eta ≤ S.D.height gamma.1) :
    letI : AlgebraicGroup S.L.carrierVariety := S.L.carrierAlgebraicGroup
    let BLevi := S.L.inclusion.closedSubgroupPreimage S.B
    let TLevi := S.L.inclusion.closedSubgroupPreimage S.T
    letI : AlgebraicGroup BLevi.carrierVariety := BLevi.carrierAlgebraicGroup
    letI : AlgebraicGroup TLevi.carrierVariety := TLevi.carrierAlgebraicGroup
    ∃ z : k, z ≠ 0 ∧
      HasHighWeight M.representation BLevi TLevi (M.rootVector (gamma, z))
        ((TorusCharacter.pullback (S.L.inclusion.preimageRestriction S.T)
          (S.D.rootWeight gamma.1))⁻¹) := by
  refine ⟨1, one_ne_zero, ?_⟩
  exact M.maximalRoot_hasHighWeight_inducedBorel S gamma hgammaMax 1 one_ne_zero

end Theory.AlgebraicGroup
