module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.Levi
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.FixedNormalizer
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.SplitNormalForm
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.SuzukiCoordinates

/-!
# Fixed Suzuki Levi generation from restricted normal forms

The split B₂ normal form and the fixed middle-node normalizer calculation
give the two fixed Bruhat cells by uniqueness. The ambient Gauss identity
expresses every coroot parameter in the positive-block/Weyl subgroup.
These arguments yield generation of the actual fixed Levi.

The three geometric results and the signed Suzuki coordinates are all
constructed in the imported modules. Substituting them into the retained
conditional reduction proves generation for every coefficient field,
including `m = 0`, without simplicity, perfectness or index hypotheses.
The torus is the entire fixed torus of the signed subsystem Levi; no
complementary parabolic torus is adjoined.

Source: GLS3, 2.3.4–8 and §2.4, especially Table 2.4 type V,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open Subgroup BlockParameters.FieldRecovery LocalIndices.SuzukiGaussData
variable {m : ℕ}

/-- Conditional assembly retaining the full split normalizer and its torus.
The geometric premises must be discharged to obtain source generation. -/
theorem suzuki_fixedLevi_le_of_normalForms (d : LocalBlockInput m)
    (C : SuzukiCoordinates d) (hG : SplitIdentity m)
    (hS : SuzukiSplitLeviNormalForm m) (hN : SuzukiFixedNormalizerForm d) :
    fixedLevi d .suzuki ≤ simpleBlock d .suzuki true ⊔ zpowers (relativeWeyl d .suzuki) :=
  suzuki_fixedLevi_le_of_bruhatCover d C hG (suzukiLeviBruhatCover_of_normalForms d hS hN)

/-- The actual fixed middle-node Levi has the two relative Bruhat cells,
with every fixed Levi torus parameter retained. -/
theorem suzukiLeviBruhatCover (d : LocalBlockInput m) : SuzukiLeviBruhatCover d :=
  suzukiLeviBruhatCover_of_normalForms d (suzukiSplitLeviNormalForm m)
    (suzuki_fixedNormalizerForm d)

/-- The positive fixed block and the literal word `[1,2,1,2]` generate the
whole fixed Levi, including its torus. This also holds at `m = 0`. -/
theorem suzuki_fixedLevi_le (d : LocalBlockInput m) :
    fixedLevi d .suzuki ≤ simpleBlock d .suzuki true ⊔ zpowers (relativeWeyl d .suzuki) :=
  suzuki_fixedLevi_le_of_bruhatCover d (suzukiCoordinates d) (Ambient.splitIdentity m)
    (suzukiLeviBruhatCover d)

/-- Generation as an equality of subgroups of the supplied fixed group. -/
theorem suzuki_fixedLevi_eq (d : LocalBlockInput m) :
    fixedLevi d .suzuki = simpleBlock d .suzuki true ⊔ zpowers (relativeWeyl d .suzuki) :=
  le_antisymm (suzuki_fixedLevi_le d) (suzuki_generated_le_fixedLevi d)

end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
