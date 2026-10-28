module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalOrdinaryAmalgam
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.OrdinaryRecognition
public import Theory.GroupTheory.Amalgam.GeneratedCompletion
public import CFSG.Quasithin.Chapter13.Section05.SourceDefs

/-!
# Original ordinary 13.5.17 ambient recognition

The original point and plane inclusions give a faithful completion in their
join. Transport the proved compatible unitary amalgam to this completion.
The source module normalizer is the required plane-root normalizer. The
source involution remains a point root under the corrected point map because
the center of the point two-core is characteristic. Its original centralizer
is the point endpoint, so the proved F.4 ordinary completion recognition forces
the endpoint join to be the whole ambient group and identifies both endpoints
with the literal unitary parabolics.

All amalgam, root-marking, normalizer, centralizer and completion inputs are
discharged from the original source Context and genuine earlier A.3.12 input.
The doubled extension is a separate branch.

Source: Aschbacher--Smith 13.5.17, printed p.922, ordinary U₄(2) branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterF.GreenBook.LieModels.UnitaryFour
open ChapterF.UnitaryTwo
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

private theorem source_point_marking_of_equiv
    (hordinary : L ⊔ (T : Subgroup G) = L)
    (e : H ≃* pointParabolic 1 (Nat.le_refl 1)) :
    (V₁.subgroupOf H).map e.toMonoidHom = PointCore.rootSubgroup := by
  obtain ⟨v,hv,e₀,he₀,hcore,hline,hmodule,hborel⟩ :=
    source_normal_ordinary_point_unitary d hA312 hH hU hn hordinary
  let a := e₀.symm.trans e
  have ha : (V₁.subgroupOf H).map e.toMonoidHom =
      ((V₁.subgroupOf H).map e₀.toMonoidHom).map a.toMonoidHom := by
    rw [map_map]
    congr 1
    ext x
    simp [a]
  rw [ha,hline]
  have : PointCore.rootSubgroup.Characteristic :=
    characteristic_of_characteristic_of_characteristic
  exact characteristic_iff_map_eq.mp this a

private theorem ordinary_recognition_of_amalgam
    (hordinary : L ⊔ (T : Subgroup G) = L)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups H (residualCentralizer L V₁ ⊔ (T : Subgroup G))
        (L ⊔ (T : Subgroup G)) hH.1.2
        (sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl))
      (amalgam 1 (Nat.le_refl 1))) :
    H ⊔ (L ⊔ (T : Subgroup G)) = ⊤ ∧
      ∃ E : G ≃* ProjectiveGroup 1 (Nat.le_refl 1),
        H.map E.toMonoidHom = pointParabolic 1 (Nat.le_refl 1) ∧
        (L ⊔ (T : Subgroup G)).map E.toMonoidHom = planeParabolic 1 (Nat.le_refl 1) := by
  let J := L ⊔ (T : Subgroup G)
  let K := H ⊔ J
  let B := residualCentralizer L V₁ ⊔ (T : Subgroup G)
  let c₀ := RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups H B J hH.1.2
    (sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl)
  let c := c₀.comapIso e.symm
  have hlf : K.subtype.comp c.left = H.subtype.comp e.left.symm.toMonoidHom := by
    ext x
    exact RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_left H B J hH.1.2
      (sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl) (e.left.symm x)
  have hrf : K.subtype.comp c.right = J.subtype.comp e.right.symm.toMonoidHom := by
    ext x
    exact RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_right H B J hH.1.2
      (sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl) (e.right.symm x)
  have hl : (K.subtype.comp c.left).range = H := by
    rw [hlf]
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact (e.left.symm x).property
    · intro hy
      refine ⟨e.left ⟨y,hy⟩,?_⟩
      change (e.left.symm (e.left ⟨y,hy⟩) : G) = y
      simp
  have hr : (K.subtype.comp c.right).range = J := by
    rw [hrf]
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact (e.right.symm x).property
    · intro hy
      refine ⟨e.right ⟨y,hy⟩,?_⟩
      change (e.right.symm (e.right ⟨y,hy⟩) : G) = y
      simp
  obtain ⟨z,hz,hoz,hcentral,hnormal,hcoreH,hcoreJ⟩ :=
    normal_source13_5_17_local_groups d hA312 hH hU hn
  have hVJ : V ≤ J := (hcoreJ ▸ pCoreIn_le 2 J)
  let : IsElementaryAbelian 2 (V.subgroupOf J) := IsElementaryAbelian.subgroupOf hVJ
  obtain ⟨eR,hVR,_,_⟩ := source_normal_ordinary_plane_unitary d hA312 hH hU hn hordinary
  have hEA : IsElementaryAbelian 2 (pCore 2 (planeParabolic 1 (Nat.le_refl 1))) :=
    hVR ▸ IsElementaryAbelian.map eR.toMonoidHom
  have hcenter : center (pCore 2 (planeParabolic 1 (Nat.le_refl 1))) = ⊤ := by
    let : IsMulCommutative (pCore 2 (planeParabolic 1 (Nat.le_refl 1))) := hEA.toIsMulCommutative
    exact center_eq_top
  have hplane : PlainFusion.sourcePlaneRootImage c K.subtype = V := by
    rw [PlainFusion.sourcePlaneRootImage,hcenter,←map_map,←MonoidHom.range_eq_map,range_subtype]
    rw [hrf]
    rw [←map_map,pCore_map_iso]
    exact hcoreJ
  have hnorm : normalizer (PlainFusion.sourcePlaneRootImage c K.subtype : Set G) =
      (K.subtype.comp c.right).range := by rw [hplane,hr]; exact hnormal
  have hzH : z ∈ H := by
    rw [←hcentral]
    exact (mem_centralizer_singleton_iff.mpr (Commute.refl z))
  let zH : H := ⟨z,hzH⟩
  have horder : orderOf (e.left zH) = 2 := by
    rw [e.left.orderOf_eq,←orderOf_injective H.subtype H.subtype_injective zH]
    exact hoz
  have hroot : e.left zH ∈ PointCore.rootSubgroup := by
    rw [←source_point_marking_of_equiv d hA312 hH hU hn hordinary e.left]
    exact mem_map_of_mem e.left.toMonoidHom hz
  have hcentral' : centralizer ({(c.left (e.left zH)).val} : Set G) ≤
      (K.subtype.comp c.left).range := by
    rw [hl]
    have hez : (c.left (e.left zH) : G) = (e.left.symm (e.left zH) : G) :=
      DFunLike.congr_fun hlf _
    rw [hez]
    simpa only [MulEquiv.symm_apply_apply] using hcentral.le
  obtain ⟨hgen,E,hE₁,hE₂⟩ :=
    OrdinaryRecognition.subgroup_completion_recognition K c hnorm (e.left zH) horder hroot hcentral'
  rw [hl] at hE₁
  rw [hr] at hE₂
  exact ⟨hgen,E,hE₁,hE₂⟩

/-- The ordinary branch of original 13.5.17 identifies the actual ambient
finite group and both original endpoints with the binary unitary model. -/
theorem source_normal_ordinary_recognition
    (hordinary : L ⊔ (T : Subgroup G) = L) :
    H ⊔ (L ⊔ (T : Subgroup G)) = ⊤ ∧
      ∃ E : G ≃* ProjectiveGroup 1 (Nat.le_refl 1),
        H.map E.toMonoidHom = pointParabolic 1 (Nat.le_refl 1) ∧
        (L ⊔ (T : Subgroup G)).map E.toMonoidHom = planeParabolic 1 (Nat.le_refl 1) := by
  obtain ⟨e⟩ := source_normal_ordinary_amalgam_unitary d hA312 hH hU hn hordinary
  exact ordinary_recognition_of_amalgam d hA312 hH hU hn hordinary e

/-- The original ordinary branch supplies the actual projective unitary
model predicate, with the field order and Hermitian conjugation specified. -/
theorem source_normal_ordinary_isPSU
    (hordinary : L ⊔ (T : Subgroup G) = L) : ClassicalGroup.IsPSU G 4 2 := by
  obtain ⟨_,E,_,_⟩ := source_normal_ordinary_recognition d hA312 hH hU hn hordinary
  refine ⟨MatrixField 1,inferInstance,inferInstance,standardForm 1 (Nat.le_refl 1),?_,?_,⟨E⟩⟩
  · simpa only [Nat.pow_one] using matrixField_card 1 (Nat.le_refl 1)
  · intro x
    change fieldConj 1 x = x ^ 2
    simpa only [Nat.pow_one] using fieldConj_apply 1 x

/-- The ordinary normal A₅ branch gives the original degree-five model
alternative of 13.5.12, as used in 13.5.17. -/
theorem source_normal_ordinary_modelConclusion
    (hordinary : L ⊔ (T : Subgroup G) = L) : ModelConclusion G 5 :=
  Or.inl ⟨rfl,Or.inl (source_normal_ordinary_isPSU d hA312 hH hU hn hordinary)⟩

end CFSG.Quasithin.Chapter13.Section05.A5Source
