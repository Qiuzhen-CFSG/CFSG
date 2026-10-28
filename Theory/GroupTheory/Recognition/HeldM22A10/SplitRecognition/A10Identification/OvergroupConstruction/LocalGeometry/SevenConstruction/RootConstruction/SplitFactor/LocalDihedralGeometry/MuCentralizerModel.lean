module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.MuCentralizerModel.Source
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.ModelAssembly

/-!
# The marked full mu-centralizer model

The corrected six-point data supplies a four-group extended by S6, with the
odd permutations fixing mu and interchanging the other two involutions.
The explicit semidirect product identifies this group with the concrete
centralizer of `(01)(23)` in A10, preserving mu. The supplied centralizer
order makes the source map an isomorphism; neither simplicity nor fusion
nor recognition of the ambient group is needed.

The two consumer applications discharge the full mu-centralizer input.
The independent order-three centralizer calculation remains explicit and
belongs to the final local-geometry assembly.

Source: Held, Illinois J. Math. 13 (1969), Lemmas 4.2 and 5.4,
DOI 10.1215/ijm/1256053756, pp.232,236–237.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer) (L : Source.SixLocalData D e)
  (hcentralizer : Nat.card (centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880)

include L hcentralizer

/-- The full centralizer of the source mu is its actual marked ten-point model. -/
public theorem exists_markedMuModel : Nonempty (MarkedMuModel D e) := by
  let f := MuCentralizerConstruction.sourceEquiv D e L hcentralizer
  refine ⟨⟨f.symm.trans MuCentralizerConstruction.modelEquiv, ?_⟩⟩
  change MuCentralizerConstruction.modelEquiv (f.symm (centralMu D e)) = modelMu
  rw [← MuCentralizerConstruction.sourceEquiv_first D e L hcentralizer]
  change MuCentralizerConstruction.modelEquiv (f.symm (f _)) = modelMu
  rw [f.symm_apply_apply, MuCentralizerConstruction.modelEquiv_first]

/-- Discharge the full centralizer model in the literal intersection calculation. -/
public theorem exists_localProduct_of_sixLocalData
    (hmodel : ∀ c : MuModel, orderOf c = 3 → Nonempty (ModelThreeCentralizer c)) :
    Nonempty (LocalProduct D e L) := by
  obtain ⟨M⟩ := exists_markedMuModel D e L hcentralizer
  exact exists_localProduct_of_muModel D e L M hmodel

/-- The source geometry now needs only the independent order-three model calculation. -/
public theorem local_geometry_of_sixLocalData [Finite G]
    (hmodel : ∀ c : MuModel, orderOf c = 3 → Nonempty (ModelThreeCentralizer c)) :
    Nat.card (centralizer ({pi D e * mu D e} : Set G) ⊓ rootCentralizer D e L : Subgroup G) = 72 ∧
    (∃ S : Sylow 2 (rootQuotient D e L), Nonempty (S ≃* DihedralGroup 4)) ∧
    (∃ t : rootQuotient D e L, orderOf t = 2 ∧
      Nonempty (centralizer ({t} : Set (rootQuotient D e L)) ≃* sevenInvolutionCentralizer)) :=
  local_geometry_of_models D e L (exists_markedMuModel D e L hcentralizer) hmodel

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry
