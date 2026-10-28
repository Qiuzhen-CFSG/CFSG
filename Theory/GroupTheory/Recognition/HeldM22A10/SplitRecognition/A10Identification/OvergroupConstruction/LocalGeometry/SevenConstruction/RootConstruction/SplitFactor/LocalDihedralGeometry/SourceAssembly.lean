module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.MuCentralizerModel
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.ThreeCentralizerModel

/-!
# Source assembly for Held's local dihedral geometry

The marked model for the full centralizer of `mu` and the product decomposition
for each of its cubic centralizers discharge both inputs of the conditional
local-geometry theorem. The resulting theorem needs only the corrected
six-point data and the supplied mu-centralizer order. The source-facing
wrapper also retains the simplicity and nonfusion hypotheses of the surrounding
Held argument.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.4, pp.236–237.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry

variable {G : Type*} [Group G] [Finite G]
  (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e)

/-- The actual intersection order, quotient Sylow type and full quotient
involution centralizer, with both marked model constructions discharged. -/
public theorem local_geometry
    (hcentralizer : Nat.card (centralizer
      ({D.a10NoncentralInvolution e} : Set G)) = 2880) :
    Nat.card (centralizer ({pi D e * mu D e} : Set G) ⊓ rootCentralizer D e L : Subgroup G) = 72 ∧
    (∃ S : Sylow 2 (rootQuotient D e L), Nonempty (S ≃* DihedralGroup 4)) ∧
    (∃ t : rootQuotient D e L, orderOf t = 2 ∧
      Nonempty (centralizer ({t} : Set (rootQuotient D e L)) ≃* sevenInvolutionCentralizer)) :=
  local_geometry_of_sixLocalData D e L hcentralizer modelThreeCentralizer_exists

/-- Held's local dihedral geometry under the full original source hypotheses. -/
public theorem local_geometry_of_source [IsSimpleGroup G]
    (_hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hcentralizer : Nat.card (centralizer
      ({D.a10NoncentralInvolution e} : Set G)) = 2880) :
    Nat.card (centralizer ({pi D e * mu D e} : Set G) ⊓ rootCentralizer D e L : Subgroup G) = 72 ∧
    (∃ S : Sylow 2 (rootQuotient D e L), Nonempty (S ≃* DihedralGroup 4)) ∧
    (∃ t : rootQuotient D e L, orderOf t = 2 ∧
      Nonempty (centralizer ({t} : Set (rootQuotient D e L)) ≃* sevenInvolutionCentralizer)) :=
  local_geometry D e L hcentralizer

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry
