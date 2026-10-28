module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.Contracts

/-!
# Connecting the two marked centralizer calculations to the source intersection

Transport the order-three element v through the marked identification of
C_G(mu). The finite model calculation then supplies product coordinates.
The tau-prime conjugation sends uv to the inverse of v and pi*mu to mu, so
both markings required by the root quotient and Sylow arguments are retained.
This conditional transport has no recognition or odd-core premise.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.4, pp.236–237.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry

private def centralizerEquiv {H K : Type*} [Group H] [Group K] (f : H ≃* K) (c : H) :
    centralizer ({c} : Set H) ≃* centralizer ({f c} : Set K) where
  toFun x := ⟨f x, mem_centralizer_singleton_iff.mpr
    ((show Commute (x : H) c from mem_centralizer_singleton_iff.mp x.property).map f).eq⟩
  invFun x := ⟨f.symm x, mem_centralizer_singleton_iff.mpr (by
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using mem_centralizer_singleton_iff.mp x.property)⟩
  left_inv x := Subtype.ext (f.symm_apply_apply x)
  right_inv x := Subtype.ext (f.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul f (x : H) (y : H))

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer) (L : Source.SixLocalData D e)
  (M : MarkedMuModel D e)

public theorem model_v_order : orderOf (M.equiv (vInMuCentralizer D e L)) = 3 := by
  rw [M.equiv.orderOf_eq, ← Subgroup.orderOf_coe]
  exact L.v_order

public theorem exists_localProduct_of_models
    (T : ModelThreeCentralizer (M.equiv (vInMuCentralizer D e L))) :
    Nonempty (LocalProduct D e L) := by
  let c := M.equiv (vInMuCentralizer D e L)
  let F := (intersectionToMuV D e L).trans (centralizerEquiv M.equiv (vInMuCentralizer D e L))
  have hi : F (intersectionInvolution D e L) = modelMuAt c := by
    apply Subtype.ext
    change M.equiv ((intersectionToMuV D e L (intersectionInvolution D e L) :
      centralizer ({vInMuCentralizer D e L} : Set (muCentralizer D e))) : muCentralizer D e) = modelMu
    rw [← M.involution]
    apply congrArg M.equiv
    apply Subtype.ext
    exact intersectionToMuV_involution D e L
  have hr : F (intersectionRoot D e L) = (modelRootAt c)⁻¹ := by
    apply Subtype.ext
    change M.equiv ((intersectionToMuV D e L (intersectionRoot D e L) :
      centralizer ({vInMuCentralizer D e L} : Set (muCentralizer D e))) : muCentralizer D e) =
        (M.equiv (vInMuCentralizer D e L))⁻¹
    rw [← map_inv]
    apply congrArg M.equiv
    apply Subtype.ext
    exact intersectionToMuV_root D e L
  refine ⟨⟨F.trans T.equiv, ?_, ?_⟩⟩
  · change T.equiv (F (intersectionInvolution D e L)) = _
    rw [hi, T.involution]
  · change (T.equiv (F (intersectionRoot D e L))).2 = 1
    rw [hr, map_inv]
    change (T.equiv (modelRootAt c)).2⁻¹ = 1
    rw [T.root, inv_one]

include M in
public theorem exists_localProduct_of_muModel
    (hmodel : ∀ c : MuModel, orderOf c = 3 → Nonempty (ModelThreeCentralizer c)) :
    Nonempty (LocalProduct D e L) := by
  obtain ⟨T⟩ := hmodel _ (model_v_order D e L M)
  exact exists_localProduct_of_models D e L M T

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry
