module

public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.CoordinateModel
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedNoFixedWeight.Restriction
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedNoFixedWeight.BlockConnected
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedNoFixedWeight.BlockRealization
public import Theory.AlgebraicGroup.Connected

/-!
# Connectedness of no-fixed-weight torus centralizers

Over an algebraically closed field of characteristic two, if `l ≠ 1`,
`m ≠ 1`, and `l ≠ m`, the literal octonion centralizer fixes both diagonal
idempotents. Its faithful Peirce action lies in the centralizer of
`diag(l,l⁻¹*m,m⁻¹)` in SL₃. That block variety is connected for every weight
multiplicity, and its polynomial octonion realization is surjective onto
the actual centralizer. Connectedness therefore passes to the centralizer.
This includes two equal weights and the scalar order-three case, where the
block variety is all of SL₃. No finite-field size hypothesis is needed.

Source: Steinberg 8.1, 8.5 and 12.5,
`refs/KGroup/GLS3/Chapter2St2.tex`, in the setting of GLS III Sections 2.1
and 2.8 (`refs/KGroup/GLS3/chapter2.tex`). This proves the no-fixed-weight
case directly in the closed octonion coordinate model.
-/

public section

open Theory.AlgebraicGroup
namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
variable {K : Type*} [Field K] [IsAlgClosed K]

/-- A regular surjective block parametrization transfers connectedness to the literal centralizer. -/
theorem centralizer_connected_of_block_parametrization (l m : Kˣ)
    (hblock : Variety.IsConnected
      (blockVariety (peirceWeights l m) (peirceWeights_prod l m)))
    (f : Variety.Morphism (blockVariety (peirceWeights l m) (peirceWeights_prod l m))
      (centralizerVariety (torus l m)))
    (hf : Function.Surjective f.toFun) :
    Variety.IsConnected (centralizerVariety (torus l m)) := by
  have h := hblock.image f.toFun f.continuous.continuousOn
  unfold Variety.IsConnected
  simpa only [Set.image_univ, hf.range_eq] using h


end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight

namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang
variable {K : Type*} [Field K] [IsAlgClosed K] [CharP K 2]

/-- A torus element with no nonconstant fixed weight has connected centralizer
in the actual octonion automorphism variety, including repeated Peirce weights. -/
theorem centralizer_connected_no_fixed_weight (l m : Kˣ)
    (hl : l ≠ 1) (hm : m ≠ 1) (hlm : l ≠ m) :
    Variety.IsConnected (centralizerVariety (torus l m)) := by
  exact NoFixedWeight.centralizer_connected_of_block_parametrization l m
    (NoFixedWeight.blockVariety_isConnected _ _)
    (NoFixedWeight.blockParametrization l m)
    (NoFixedWeight.blockParametrization_surjective l m hl hm hlm)

end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang
