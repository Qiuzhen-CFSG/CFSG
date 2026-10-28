/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianAlternatingConwayProduct.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source revision: 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianScalarConwayProduct
public import Theory.AtlasPort.Janko2.Algebra.GoldenFourAlternating

/-!
# IcosianAlternatingConwayProduct

The scalar sign quotient is identified with the concrete alternating group on five points.
Transporting the two commuting quotient embeddings gives an injective map from A5 times J2.

Source: Gerald Höhn, `Atlas/Conway/IcosianAlternatingConwayProduct.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and the definition bodies
needed by the source coordinate calculations; source statements are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra

/-- The scalar sign quotient is the actual A5, via its five-point projective action. -/
def icosianScalarProjectiveAlternating :
    IcosianScalarProjectiveModel ≃* alternatingGroup (Fin 5) :=
  icosianScalarProjectiveSL.trans goldenFourSLAlternatingFive

/-- The concrete A5 times quaternionic projective group inside the retained Co1. -/
def icosianAlternatingProjectiveToCo1 :
    alternatingGroup (Fin 5) × IcosianProjectiveModel →* LeechCentralQuotient :=
  icosianScalarProjectiveProductToCo1.comp
    (icosianScalarProjectiveAlternating.symm.prodCongr (MulEquiv.refl _)).toMonoidHom

theorem icosianAlternatingProjectiveToCo1_injective :
    Function.Injective icosianAlternatingProjectiveToCo1 :=
  icosianScalarProjectiveProductToCo1_injective.comp
    (icosianScalarProjectiveAlternating.symm.prodCongr (MulEquiv.refl _)).injective

end Atlas.Conway
