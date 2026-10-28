module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.Parabolics
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.RootBorel
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.Cosets
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.Separation
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.LinearCover
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.SuzukiCoordinates

/-!
# Local indices of the positive Ree root parabolics

The root grading proves that a negative simple block meets the root Borel
trivially. Its elements therefore give distinct actual Borel cosets. A
rank-one cover adds at most one coset, and oddness of the supplied unipotent
index forces that extra coset to occur. The type VI block has `q` elements;
the type V chart has `q²` elements, where `q = 2^(2*m+1)`.

The final theorems assemble the constructed rank-one covers and the complete
signed Suzuki coordinates, discharging those inputs to the counting lemmas.
They retain the supplied odd unipotent index and equality of the split and
diagonal tori; neither simplicity nor perfectness is needed. The Suzuki
cover uses `1 ≤ m`, while the linear calculation also applies at `m = 0`.

Source: GLS3, Theorems 2.3.4–8, Table 2.4 types V and VI, and 2.6.5,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices
open LargeLocalSeeds BlockParameters.FieldRecovery
variable {m : ℕ}

/-- The linear local index from rank-one coverage, with separation discharged. -/
theorem linear_relIndex_of_rankOneCover (d : LocalBlockInput m)
    (hindex : Odd (standardUnipotent d).index)
    (hT : Parabolics.splitTorus m = Parabolics.diagonalTorus m)
    (n : rootParabolic d .linear) (hc : RankOneCover d .linear n) :
    (rootBorel d).relIndex (rootBorel d ⊔ simpleBlock d .linear false) =
      2 ^ (2 * m + 1) + 1 :=
  linear_relIndex_of_cover d hindex n (negativeBlock_disjoint_rootBorel d hT .linear) hc

/-- The Suzuki local index from coordinates and coverage, with separation discharged. -/
theorem suzuki_relIndex_of_rankOneCover (d : LocalBlockInput m)
    (hindex : Odd (standardUnipotent d).index)
    (hT : Parabolics.splitTorus m = Parabolics.diagonalTorus m)
    (C : SuzukiCoordinates d)
    (n : rootParabolic d .suzuki) (hc : RankOneCover d .suzuki n) :
    (rootBorel d).relIndex (rootBorel d ⊔ simpleBlock d .suzuki false) =
      (2 ^ (2 * m + 1)) ^ 2 + 1 :=
  suzuki_relIndex_of_cover d hindex C n (negativeBlock_disjoint_rootBorel d hT .suzuki) hc

/-- The positive linear root parabolic has Borel index `q + 1`, where
`q = 2^(2*m+1)`. The actual coset cover and separation are both proved. -/
theorem linear_relIndex (d : LocalBlockInput m)
    (hindex : Odd (standardUnipotent d).index)
    (hT : Parabolics.splitTorus m = Parabolics.diagonalTorus m) :
    (rootBorel d).relIndex (rootBorel d ⊔ simpleBlock d .linear false) =
      2 ^ (2 * m + 1) + 1 := by
  obtain ⟨n, hc⟩ := exists_linear_rankOneCover d hT
  exact linear_relIndex_of_rankOneCover d hindex hT n hc

/-- The positive Suzuki root parabolic has Borel index `q² + 1`, where
`q = 2^(2*m+1)`. Complete block coordinates, actual coset coverage and
block–Borel separation are all discharged. -/
theorem suzuki_relIndex (hm : 1 ≤ m) (d : LocalBlockInput m)
    (hindex : Odd (standardUnipotent d).index)
    (hT : Parabolics.splitTorus m = Parabolics.diagonalTorus m) :
    (rootBorel d).relIndex (rootBorel d ⊔ simpleBlock d .suzuki false) =
      (2 ^ (2 * m + 1)) ^ 2 + 1 := by
  obtain ⟨n, hc⟩ := exists_suzuki_rankOneCover hm d hT (suzukiCoordinates d)
  exact suzuki_relIndex_of_rankOneCover d hindex hT (suzukiCoordinates d) n hc

end ReeF4.LocalBlockInput.PairRigidity.LocalIndices
