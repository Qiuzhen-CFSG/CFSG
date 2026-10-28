module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalDoubledPoint
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalDoubledUpgrade
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.OverlapRigidityFull
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalDoubledPlaneRestriction
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalDoubledCompletion
/-!
# The compatible doubled unitary amalgam in the original normal A₅ branch

Recognize the ordinary point subgroup O²(H)V and restrict the marked full
plane map to L. Their overlap discrepancy preserves the original module V.
Correct it by the ordinary unitary overlap factorization, choosing its plane
correction to extend to the full plane and preserve the full overlap. The
index-two extension then supplies the full point map with both inclusion
squares. All comparison and compatibility inputs come from the original
Context, A.3.12, nonabelian U_H, residual normality and LT≠L.

The actual F.5 consumer constructs the faithful completion in H∨LT and
recovers the original endpoint ranges and root images V₁,V. The terminal
F.5 ambient recognition remains a separate theorem.

Source: Aschbacher--Smith 13.5.17, printed p.922, doubled normal A₅ branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterF.GreenBook.LieModels.UnitaryFour
open ChapterF.UnitaryTwo

private def endpointRestriction {G K : Type*} [Group G] [Group K]
    {S B : Subgroup G} {S' B' : Subgroup K} (h : B≤S) (h' : B'≤S')
    (e : S ≃* S') (he : (B.subgroupOf S).map e.toMonoidHom = B'.subgroupOf S') : B ≃* B' :=
  (subgroupOfEquivOfLe h).symm.trans ((e.subgroupMap _).trans
    ((MulEquiv.subgroupCongr he).trans (subgroupOfEquivOfLe h')))

private theorem endpointRestriction_val {G K : Type*} [Group G] [Group K]
    {S B : Subgroup G} {S' B' : Subgroup K} (h : B≤S) (h' : B'≤S')
    (e : S ≃* S') (he : (B.subgroupOf S).map e.toMonoidHom = B'.subgroupOf S') (b : B) :
    (endpointRestriction h h' e he b : K) = (e ⟨b,h b.property⟩ : K) := by rfl

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn


private theorem doubled_amalgam_of_marked_planes
    (hdoubled : L ⊔ (T : Subgroup G) ≠ L)
    (eR : L ≃* planeParabolic 1 (Nat.le_refl 1))
    (hRV : (V.subgroupOf L).map eR.toMonoidHom=pCore 2 (planeParabolic 1 (Nat.le_refl 1)))
    (hRB : (((residualCentralizer L V₁ ⊔ (T : Subgroup G)) ⊓ L).subgroupOf L).map eR.toMonoidHom =
      (overlap 1 (Nat.le_refl 1)).subgroupOf (planeParabolic 1 (Nat.le_refl 1)))
    (eM : (L ⊔ (T : Subgroup G) : Subgroup G) ≃* Extension.plane 1 (Nat.le_refl 1))
    (hBM : ((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf
        (L ⊔ (T : Subgroup G))).map eM.toMonoidHom =
      (Extension.overlap 1 (Nat.le_refl 1)).subgroupOf (Extension.plane 1 (Nat.le_refl 1)))
    (hMR : ∀ l : L,
      (eM ⟨l, mem_sup_left l.property⟩ : Extension.ProjectiveExtension 1 (Nat.le_refl 1)) =
        SemidirectProduct.inl (eR l : ProjectiveGroup 1 (Nat.le_refl 1)))
    (E : BinaryPermutation.AlternatingFiveExtension.AlternatingModel ≃* planeParabolic 1 (Nat.le_refl 1))
    (hz : E (SemidirectProduct.inl (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.z))=ModelClasses.longRight)
    (hV : (SemidirectProduct.inl : BinaryPermutation.AlternatingFiveExtension.V →*
      BinaryPermutation.AlternatingFiveExtension.AlternatingModel).range.map E.toMonoidHom=pCore 2 (planeParabolic 1 (Nat.le_refl 1)))
    (hB : BinaryPermutation.AlternatingFiveExtension.borelEmbedding.range.map E.toMonoidHom=
      (overlap 1 (Nat.le_refl 1)).subgroupOf (planeParabolic 1 (Nat.le_refl 1)))
    (F : BinaryPermutation.AlternatingFiveExtension.OverlapFactorizationExtension.SymmetricModel ≃*
      Extension.plane 1 (Nat.le_refl 1))
    (hFz : F (SemidirectProduct.inl (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.z))=ExtendedAffinePlane.longRight)
    (hFE : ∀ x, F (BinaryPermutation.AlternatingFiveExtension.OverlapFactorizationExtension.symmetricEmbedding x)=
      Extension.binaryPlaneInclusion (E x)) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups H
        (residualCentralizer L V₁ ⊔ (T : Subgroup G)) (L ⊔ (T : Subgroup G))
        hH.1.2 (sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl))
      (Extension.amalgam 1 (Nat.le_refl 1))) := by
  obtain ⟨eP,hPV,hPB⟩ := source_normal_point_base_ambient_unitary d hA312 hH hU hn
  let B := residualCentralizer L V₁ ⊔ (T : Subgroup G)
  let J := (pResidual 2 H).map H.subtype ⊔ V
  let C := B ⊓ L
  have hCJ : C≤J := (normal_point_subgroup_overlap d hA312 hH hU hn).ge.trans inf_le_right
  have hCP : (C.subgroupOf J).map eP.toMonoidHom =
      (overlap 1 (Nat.le_refl 1)).subgroupOf (pointParabolic 1 (Nat.le_refl 1)) := by
    have he : C.subgroupOf J=B.subgroupOf J := by
      ext x
      change (x:G)∈(residualCentralizer L V₁ ⊔ (T : Subgroup G)) ⊓ L ↔ (x:G)∈B
      rw [←normal_point_subgroup_overlap d hA312 hH hU hn]
      exact and_iff_left x.property
    rw [he]
    exact hPB
  have hBP' : overlap 1 (Nat.le_refl 1) ≤ pointParabolic 1 (Nat.le_refl 1) := by
    rw [←exact_overlap]; exact inf_le_left
  have hBR' : overlap 1 (Nat.le_refl 1) ≤ planeParabolic 1 (Nat.le_refl 1) := by
    rw [←exact_overlap]; exact inf_le_right
  let uP := endpointRestriction hCJ hBP' eP hCP
  let uR := endpointRestriction (show C≤L from inf_le_right) hBR' eR hRB
  have hP (b : C) : (uP b : ProjectiveGroup 1 (Nat.le_refl 1))∈InvolutionPlacement.planeCore ↔ (b:G)∈V := by
    rw [endpointRestriction_val]
    change eP ⟨b,hCJ b.property⟩ ∈ PointInvolution.pointModule ↔ _
    rw [←hPV,mem_map_equiv,eP.symm_apply_apply]
    rfl
  have hR (b : C) : (uR b : ProjectiveGroup 1 (Nat.le_refl 1))∈InvolutionPlacement.planeCore ↔ (b:G)∈V := by
    rw [endpointRestriction_val,OverlapRigidity.planeCore_mem,←hRV,
      mem_map_equiv,eR.symm_apply_apply]
    rfl
  let δ := uP.symm.trans uR
  have hδ : ∀ b : overlap 1 (Nat.le_refl 1), (b:ProjectiveGroup 1 (Nat.le_refl 1))∈InvolutionPlacement.planeCore →
      (δ b : ProjectiveGroup 1 (Nat.le_refl 1))∈InvolutionPlacement.planeCore := by
    intro b hb
    change (uR (uP.symm b) : ProjectiveGroup 1 (Nat.le_refl 1))∈InvolutionPlacement.planeCore
    apply (hR _).mpr
    apply (hP _).mp
    simpa only [MulEquiv.apply_symm_apply] using hb
  let f : Iso (RankTwoAmalgam.ofSubgroups J C L hCJ inf_le_right)
      (twistRight (amalgam 1 (Nat.le_refl 1)) δ) := {
    left := eP
    middle := uP
    right := eR
    left_commutes b := by
      apply Subtype.ext
      exact (endpointRestriction_val hCJ hBP' eP hCP b).symm
    right_commutes b := by
      apply Subtype.ext
      change (eR ⟨b,b.property.2⟩ : ProjectiveGroup 1 (Nat.le_refl 1)) =
        (uR (uP.symm (uP b)) : ProjectiveGroup 1 (Nat.le_refl 1))
      rw [uP.symm_apply_apply]
      exact (endpointRestriction_val inf_le_right hBR' eR hRB b).symm }
  obtain ⟨corr,fcorr,hfcorr,hcompat⟩ :=
    OverlapRigidityFull.iso_with_full_extension E hz hV hB F hFz hFE δ hδ
  apply source_normal_doubled_amalgam_of_compatible_maps d hA312 hH hU hn hdoubled
    (f.trans corr) (eM.trans fcorr)
  · change ((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf
        (L ⊔ (T : Subgroup G))).map (fcorr.toMonoidHom.comp eM.toMonoidHom) = _
    rw [←map_map,hBM,hfcorr]
  · intro l
    have hh : eM ⟨l,mem_sup_left l.property⟩=Extension.binaryPlaneInclusion (eR l) :=
      Subtype.ext (hMR l)
    change (fcorr (eM ⟨l,mem_sup_left l.property⟩) : Extension.ProjectiveExtension 1 (Nat.le_refl 1)) = _
    rw [hh,hcompat]
    rfl
/-- The original doubled source inclusion amalgam is the literal extended
binary-unitary amalgam, with both commuting squares. -/
theorem source_normal_doubled_amalgam_unitary
    (hdoubled : L ⊔ (T : Subgroup G) ≠ L) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups H
        (residualCentralizer L V₁ ⊔ (T : Subgroup G)) (L ⊔ (T : Subgroup G))
        hH.1.2 (sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl))
      (Extension.amalgam 1 (Nat.le_refl 1))) := by
  obtain ⟨eM,eR,_,_,hBM,_,hRV,hRB,hMR⟩ :=
    source_normal_doubled_plane_pair d hA312 hH hU hn hdoubled
  obtain ⟨F,E,hFz,_,_,hz,hV,hB,hFE⟩ :=
    ExtendedAffinePlane.exists_compatible_marked_plane_equivs
  exact doubled_amalgam_of_marked_planes d hA312 hH hU hn hdoubled
    eR hRV hRB eM hBM (fun l => congrArg Subtype.val (hMR l)) E hz hV hB F hFz hFE

/-- The doubled branch supplies the genuine F.5 hypotheses on the completion
in the join of the original endpoints, with both source root images retained. -/
theorem source_normal_doubled_completion
    (hdoubled : L ⊔ (T : Subgroup G) ≠ L) :
    ∃ c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 (Nat.le_refl 1))
        (G := (H ⊔ (L ⊔ (T : Subgroup G)) : Subgroup G)),
      ∃ z : pointParabolic 1 (Nat.le_refl 1),
        ChapterF.Section05.Source.Hypotheses c (H ⊔ (L ⊔ (T : Subgroup G))).subtype z ∧
        ((H ⊔ (L ⊔ (T : Subgroup G))).subtype.comp c.left).range=H ∧
        ((H ⊔ (L ⊔ (T : Subgroup G))).subtype.comp c.right).range=L ⊔ (T : Subgroup G) ∧
        ChapterF.Section05.Source.pointRootImage c (H ⊔ (L ⊔ (T : Subgroup G))).subtype=V₁ ∧
        ChapterF.Section05.Source.planeRootImage c (H ⊔ (L ⊔ (T : Subgroup G))).subtype=V := by
  obtain ⟨e⟩ := source_normal_doubled_amalgam_unitary d hA312 hH hU hn hdoubled
  exact source_normal_doubled_completion_of_amalgam d hA312 hH hU hn e
end CFSG.Quasithin.Chapter13.Section05.A5Source
