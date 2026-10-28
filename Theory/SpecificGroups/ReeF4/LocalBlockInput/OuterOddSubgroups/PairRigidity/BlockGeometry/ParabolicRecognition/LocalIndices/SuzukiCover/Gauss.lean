module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.RankOne
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.FourDimensional
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient

/-!
# The local Suzuki inversion law from its literal split-root identity

The scalar and four-dimensional calculations are complete in `Gauss.Coordinates`
and `Gauss.FourDimensional`. The remaining `SplitIdentity` is an explicit
word equality in the actual 52-dimensional split Ree carrier. Given that
equality, cancelling the negative word leaves a product of two coroot words
and a positive Suzuki word. Both factors lie in the split Borel, giving the
published `SuzukiGauss` predicate after restriction to the supplied fixed group.

The ambient matrix calculation in `Gauss.Ambient` supplies the literal identity
on the full carrier, so the final theorem below discharges the local inversion
law. No simplicity, perfectness, index or torus-identification hypothesis is
needed by the calculation; the source-facing theorem retains the latter inputs
for compatibility with its local-index interface.

Source: GLS3, 2.3.4--8, Table 2.4 type V and 2.6.5,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices
open BlockParameters.FieldRecovery Parabolics SuzukiGaussData
variable {m : ℕ}

/-- The literal split-root identity suffices: its coroot factor is already in
the split torus, and its positive Suzuki factor is already in the Borel. -/
theorem suzukiGauss_of_splitIdentity (d : LocalBlockInput m) (C : SuzukiCoordinates d)
    (h : SuzukiGaussData.SplitIdentity m) : SuzukiGauss d C := by
  intro t u htu
  have hn := SuzukiGaussData.norm_ne_zero t u htu
  refine ⟨negativeFirst t u, negativeSecond t u, ?_⟩
  change (suzukiWord m false (negativeFirst t u) (negativeSecond t u))⁻¹ *
    Binary.FixedGeometry.simpleWord m [1,2,1,2] * suzukiWord m false t u ∈ splitBorel m
  rw [mul_assoc, h t u hn, mul_assoc, inv_mul_cancel_left]
  apply (splitBorel m).mul_mem
  · exact (le_sup_right : splitTorus m ≤ splitBorel m) (torusFactor_mem _)
  · exact suzukiElement_positive_mem_borel d C (positiveFirst t u) (positiveSecond t u)

/-- The ambient matrix calculation supplies the literal split-root identity for
every Ree coefficient field. The displayed local hypotheses are retained in
the source-facing interface, although this particular root calculation does
not use them. -/
theorem suzukiGauss (_hm : 1 ≤ m) (d : LocalBlockInput m) (C : SuzukiCoordinates d)
    (_hT : Parabolics.splitTorus m = Parabolics.diagonalTorus m) : SuzukiGauss d C := by
  exact suzukiGauss_of_splitIdentity d C (SuzukiGaussData.Ambient.splitIdentity m)

end ReeF4.LocalBlockInput.PairRigidity.LocalIndices
