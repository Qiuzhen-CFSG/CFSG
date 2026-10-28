module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.LocalActions.RootGeometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.LocalActions.Semilinear.Transport
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.LocalActions.Semilinear.ParameterRecovery
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FixedTorus

/-!
# Common field coordinates for preserved Ree simple blocks

Preservation of the four full signed simple blocks determines one field
automorphism and compatible diagonal parameters. Parameter recovery derives
additivity, scaled multiplicativity and compatibility of the linear and Suzuki
coordinates, including both signs and the central Suzuki coordinate.
The coroot-word realization places the inverse diagonal matrix in the actual
fixed group. Transport to the canonical model and diagonal cancellation then
give one inner correction and one field automorphism on all four blocks.

The matrix convention is `T⁻¹ * x * T`, so the inner representative is `T⁻¹`.
All parameter-recovery and realization premises are discharged here. No
simplicity, perfectness or order condition on the automorphism is required.

This is the local coordinate step in GLS3, 2.5.1(b,c), and Steinberg,
Theorem 36 (`refs/KGroup/GLS3/chapter2.tex` and `Chapter2St1.tex`).
-/

public section

namespace ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.LocalActions.Semilinear

open Theory.AlgebraicGroup
open LocalBlockInput.PairRigidity.BlockParameters

/-- One actual inner correction leaves the same entrywise field automorphism
on every element of all four full signed simple blocks. -/
theorem exists_common_field (m : ℕ) (hm : 1 ≤ m)
    (hindex : Odd (unipotent m).index)
    (hgen : seed m .suzuki ⊔ seed m .linear = ⊤)
    (c : MulAut (Model m)) (hp : PreservesUnipotentPair m c)
    (hc : PreservesSimpleBlocks m c) :
    ∃ (z : Model m) (σ : CoefficientField m ≃+* CoefficientField m),
      ∀ s positive, ∀ x ∈ simpleBlock m s positive,
        ∀ i j : F4Chevalley.BasisIndex,
          (matrixRepresentation m (((MulAut.conj z)⁻¹ * c) x) : MatrixCarrier m) i j =
            σ ((matrixRepresentation m x : MatrixCarrier m) i j) :=
  common_field_of_recovery_and_realization (canonicalLocalBlockInput m) c
    (exists_canonical_torusFieldAction hm hindex hgen c hp hc)
    (exists_fixedGroup_torusMatrix_inv (canonicalLocalBlockInput m))

end ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.LocalActions.Semilinear
