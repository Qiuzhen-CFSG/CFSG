module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.ThreeCentralizerModel.Classes
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.ModelTransport

/-!
# The marked cubic centralizers in the concrete mu model

Every element of order three in C_A10((01)(23)) is conjugate inside that
centralizer to (456) or (456)(789). For both representatives, the block and
tail coordinates give a genuine product isomorphism with C3 × C_A7((01)(23)).
Conjugation transports this isomorphism while fixing the marked involution
and carrying the root into the first factor.

This completes the finite-model input to `exists_localProduct_of_muModel`.
The application below retains the independent marked ambient mu-centralizer
identification, which is supplied by the parent source-theorem assembly.

Source: Held, DOI 10.1215/ijm/1256053756, Lemma 5.4, pp.236–237.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry

private def transportModel (f : MuModel ≃* MuModel) (hf : f modelMu = modelMu)
    (c : MuModel) (T : ModelThreeCentralizer (f c)) : ModelThreeCentralizer c where
  equiv := (ThreeCentralizer.centralizerEquiv f c).trans T.equiv
  involution := by
    have h : ThreeCentralizer.centralizerEquiv f c (modelMuAt c) = modelMuAt (f c) :=
      Subtype.ext hf
    change T.equiv (ThreeCentralizer.centralizerEquiv f c (modelMuAt c)) = _
    rw [h, T.involution]
  root := by
    change (T.equiv (modelRootAt (f c))).2 = 1
    exact T.root

public theorem modelThreeCentralizer_exists (c : MuModel) (hc : orderOf c = 3) :
    Nonempty (ModelThreeCentralizer c) := by
  obtain ⟨t, q, hq⟩ := ThreeCentralizer.representative_conjugacy c hc
  have hq' : (MulAut.conj q) c = ThreeCentralizer.representative t := hq
  have hmu : (MulAut.conj q) modelMu = modelMu := by
    change q * modelMu * q⁻¹ = modelMu
    have h : q * modelMu = modelMu * q :=
      Subtype.ext (mem_centralizer_singleton_iff.mp q.property)
    rw [h, mul_inv_cancel_right]
  have T : ModelThreeCentralizer ((MulAut.conj q) c) := by
    rw [hq']
    exact ThreeCentralizer.representativeModel t
  exact ⟨transportModel (MulAut.conj q) hmu c T⟩

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e)

/-- The concrete cubic calculation discharges the finite-model premise of
`exists_localProduct_of_muModel`. The independent marked identification of
`C_G(mu)` remains the parent's input. -/
public theorem exists_localProduct_of_markedMuModel (M : MarkedMuModel D e) :
    Nonempty (LocalProduct D e L) :=
  exists_localProduct_of_muModel D e L M modelThreeCentralizer_exists

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry
