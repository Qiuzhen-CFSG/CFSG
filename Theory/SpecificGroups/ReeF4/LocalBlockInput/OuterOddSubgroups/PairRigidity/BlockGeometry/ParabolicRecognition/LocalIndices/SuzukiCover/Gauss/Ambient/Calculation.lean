module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient.Calculation.Repeated
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient.Calculation.Four
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient.Calculation.CartanBlock
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient.Calculation.FiveBlock

/-!
# Assembly of the full Suzuki Gauss calculation

The verified decomposition of all 52 coordinates reduces the equation to
one twelve-dimensional block, four five-dimensional blocks, four
four-dimensional blocks and four fixed lines. The complete Cartan and
five-dimensional calculations, the checked four-dimensional model comparison
and the fixed-line calculation prove all four representative equations.
Transport between repeated blocks and the full matrix-algebra decomposition
then give `gaussIdentity`, including every Cartan column.

Source: GLS3, Table 2.4 type V, 2.3.4--8 and 2.6.5,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient

/-- Full-matrix assembly from the two remaining nontrivial block calculations. -/
theorem gaussIdentity_of_remaining_blocks (m : ℕ)
    (h12 : Calculation.BlockGauss m 0) (h5 : Calculation.BlockGauss m 1) :
    GaussIdentity m :=
  Calculation.gauss_of_representatives h12 h5
    (Calculation.blockGauss_fourDimensional m) (Calculation.blockGauss_nine m)

/-- The Suzuki Gauss factorization on all 52 coordinates, with no extra premises. -/
theorem gaussIdentity (m : ℕ) : GaussIdentity m :=
  gaussIdentity_of_remaining_blocks m
    (Calculation.blockGauss_cartan m) (Calculation.blockGauss_fiveDimensional m)

end ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient
end
