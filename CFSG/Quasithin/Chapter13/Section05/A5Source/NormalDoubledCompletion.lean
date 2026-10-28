module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPointCentralizer
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPointStructure
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PointOverlapExtension
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PointQuaternion
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.AffinePlane
public import CFSG.Quasithin.ChapterF.Section05.Source
public import Theory.GroupTheory.Amalgam.GeneratedCompletion
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines
public import Mathlib.GroupTheory.IsPerfect

/-!
# Original doubled normal-A₅ completion hypotheses

Transport the genuine completion in the join of the original endpoints through
a compatible doubled unitary amalgam isomorphism. The ordinary parabolics are
normal in their extended endpoints. Their two-cores therefore map into the
original two-cores; equality of orders identifies them. Centers recover the
source line and module, so the original local normalizer and centralizer
identities supply the literal F.4.31 hypotheses used in Chapter F.5.

The point root is central in the ordinary point endpoint and belongs to its
prime-to-two residual, establishing the precise source root condition. Ambient
nonabelian simplicity supplies the two-residual condition. The sole remaining
input is the doubled amalgam isomorphism, produced by the parent assembly.

Source: Aschbacher--Smith 13.5.17, printed p.922, and F.4.31, pp.290–291.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open CFSG.Quasithin.ChapterF.UnitaryTwo

namespace CFSG.Quasithin.Chapter13.Section05.A5Source.NormalDoubledCompletion
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.UnitaryTwo
local notation "hn" => Nat.le_refl 1
local notation "P" => pointParabolic 1 hn
local notation "Q" => planeParabolic 1 hn
local notation "EP" => Extension.point 1 hn
local notation "EQ" => Extension.plane 1 hn
local notation "pi" => ChapterF.Section05.Source.pointInclusion
local notation "qi" => ChapterF.Section05.Source.planeInclusion

private def ordinaryPlane : Subgroup EQ :=
  (SemidirectProduct.rightHom.comp (EQ).subtype).ker
private instance : ordinaryPlane.Normal := MonoidHom.normal_ker _
private def ordinaryPlaneEquiv : Q ≃* ordinaryPlane where
  toFun p := ⟨⟨SemidirectProduct.inl p.val,
    (Extension.mem_plane 1 hn _).mpr p.property⟩, rfl⟩
  invFun p := ⟨p.val.val.left, (Extension.mem_plane 1 hn _).mp p.val.property⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact p.property.symm
  map_mul' p q := by
    apply Subtype.ext
    apply Subtype.ext
    exact SemidirectProduct.inl.map_mul p.val q.val

private theorem pointInclusion_injective : Function.Injective pi := by
  intro x y h
  apply Subtype.ext
  exact SemidirectProduct.inl_injective (congrArg Subtype.val h)
private theorem planeInclusion_injective : Function.Injective qi := by
  intro x y h
  apply Subtype.ext
  exact SemidirectProduct.inl_injective (congrArg Subtype.val h)

private theorem point_core_normal : ((pCore 2 P).map pi).Normal := by
  have hi : pi = PointOverlapExtension.ordinaryPoint.subtype.comp
      PointOverlapExtension.ordinaryPointEquiv.toMonoidHom := rfl
  rw [hi,←map_map,pCore_map_iso]
  exact ConjAct.normal_of_characteristic_of_normal
private theorem plane_core_normal : ((pCore 2 Q).map qi).Normal := by
  have hi : qi = ordinaryPlane.subtype.comp ordinaryPlaneEquiv.toMonoidHom := rfl
  rw [hi,←map_map,pCore_map_iso]
  exact ConjAct.normal_of_characteristic_of_normal

private theorem point_core_card : Nat.card (pCore 2 P)=32 :=
  PointQuaternion.projectivePointQuaternionData.card
private theorem plane_core_card : Nat.card (pCore 2 Q)=16 := by
  rw [BinaryCompletion.plane_eq_local,L2TwoCore_card]
  norm_num
private theorem plane_core_center : center (pCore 2 Q)=⊤ := by
  rw [BinaryCompletion.plane_eq_local]
  exact center_eq_top

private theorem root_le_source : PointCore.rootSubgroup ≤ ChapterF.Section05.Source.rootSubgroup := by
  intro z hz
  have hc := PointCore.rootSubgroup_central hz
  have hcore : z∈pCore 2 P := (map_subtype_le _) hz
  have hr := le_primeToResidual_of_isPGroup pCore_isPGroup hcore
  refine ⟨⟨z,hr⟩,mem_center_iff.mpr ?_,rfl⟩
  intro y
  exact Subtype.ext (mem_center_iff.mp hc y)
end CFSG.Quasithin.Chapter13.Section05.A5Source.NormalDoubledCompletion

namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08 NormalDoubledCompletion
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.UnitaryTwo
local notation "h1" => Nat.le_refl 1
local notation "P" => pointParabolic 1 h1
local notation "Q" => planeParabolic 1 h1
local notation "pi" => ChapterF.Section05.Source.pointInclusion
local notation "qi" => ChapterF.Section05.Source.planeInclusion
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

/-- The actual doubled completion satisfies the original F.5 source hypotheses,
with both original endpoint and root images retained. -/
theorem source_normal_doubled_completion_of_amalgam
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups H (residualCentralizer L V₁ ⊔ (T : Subgroup G))
        (L ⊔ (T : Subgroup G)) hH.1.2
        (sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl))
      (Extension.amalgam 1 h1)) :
    ∃ c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 h1)
        (G := (H ⊔ (L ⊔ (T : Subgroup G)) : Subgroup G)),
      ∃ z : P, ChapterF.Section05.Source.Hypotheses c (H ⊔ (L ⊔ (T : Subgroup G))).subtype z ∧
        ((H ⊔ (L ⊔ (T : Subgroup G))).subtype.comp c.left).range=H ∧
        ((H ⊔ (L ⊔ (T : Subgroup G))).subtype.comp c.right).range=L ⊔ (T : Subgroup G) ∧
        ChapterF.Section05.Source.pointRootImage c (H ⊔ (L ⊔ (T : Subgroup G))).subtype=V₁ ∧
        ChapterF.Section05.Source.planeRootImage c (H ⊔ (L ⊔ (T : Subgroup G))).subtype=V := by
  let M := L ⊔ (T : Subgroup G)
  let K := H ⊔ M
  let B := residualCentralizer L V₁ ⊔ (T : Subgroup G)
  let c₀ := RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups H B M hH.1.2
    (sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl)
  let c := c₀.comapIso e.symm
  have hlf : K.subtype.comp c.left = H.subtype.comp e.left.symm.toMonoidHom := by
    ext x
    exact RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_left H B M hH.1.2
      (sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl) (e.left.symm x)
  have hrf : K.subtype.comp c.right = M.subtype.comp e.right.symm.toMonoidHom := by
    ext x
    exact RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_right H B M hH.1.2
      (sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl) (e.right.symm x)
  have hl : (K.subtype.comp c.left).range = H := by
    rw [hlf,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.left.symm.surjective, ←MonoidHom.range_eq_map,range_subtype]
  have hr : (K.subtype.comp c.right).range = M := by
    rw [hrf,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.right.symm.surjective, ←MonoidHom.range_eq_map,range_subtype]
  obtain ⟨z,hz,hoz,hcentral,hnormal,hcoreH,hcoreM⟩ :=
    normal_source13_5_17_local_groups d hA312 hH hU hn
  obtain ⟨q,hcenterH⟩ := normal_point_core_geometry d hA312 hH hU hn
  let fP : P →* H := e.left.symm.toMonoidHom.comp pi
  let fQ : Q →* M := e.right.symm.toMonoidHom.comp qi
  have hfP : Function.Injective fP := e.left.symm.injective.comp pointInclusion_injective
  have hfQ : Function.Injective fQ := e.right.symm.injective.comp planeInclusion_injective
  have hPnormal : ((pCore 2 P).map fP).Normal := by
    rw [show fP = e.left.symm.toMonoidHom.comp pi from rfl,←map_map]
    exact point_core_normal.map _ e.left.symm.surjective
  have hQnormal : ((pCore 2 Q).map fQ).Normal := by
    rw [show fQ = e.right.symm.toMonoidHom.comp qi from rfl,←map_map]
    exact plane_core_normal.map _ e.right.symm.surjective
  have hcP : (pCore 2 P).map fP=pCore 2 H := by
    have hle : (pCore 2 P).map fP ≤ pCore 2 H :=
      le_sSup ⟨hPnormal,pCore_isPGroup.map fP⟩
    apply eq_of_le_of_card_ge hle
    rw [card_map_of_injective hfP,point_core_card,q.card]
  have hVcard : Nat.card V=16 := d.module_card
  have hMcard : Nat.card (pCore 2 M)=16 := by
    have hh := congrArg (fun A : Subgroup G => Nat.card A) hcoreM
    change Nat.card ((pCore 2 M).map M.subtype)=Nat.card V at hh
    rw [card_map_of_injective M.subtype_injective,hVcard] at hh
    exact hh
  have hcQ : (pCore 2 Q).map fQ=pCore 2 M := by
    have hle : (pCore 2 Q).map fQ ≤ pCore 2 M :=
      le_sSup ⟨hQnormal,pCore_isPGroup.map fQ⟩
    apply eq_of_le_of_card_ge hle
    rw [card_map_of_injective hfQ,plane_core_card,hMcard]
  have hpoint : ChapterF.Section05.Source.pointRootImage c K.subtype=V₁ := by
    rw [ChapterF.Section05.Source.pointRootImage,hlf]
    change (center (pCore 2 P)).map (H.subtype.comp (fP.comp (pCore 2 P).subtype))=V₁
    rw [←map_map,←map_center_image_of_injective _ fP hfP,hcP,map_map]
    exact hcenterH
  have hplane : ChapterF.Section05.Source.planeRootImage c K.subtype=V := by
    rw [ChapterF.Section05.Source.planeRootImage,plane_core_center,
      ←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype,hrf]
    change (pCore 2 Q).map (M.subtype.comp fQ)=V
    rw [←map_map,hcQ]
    exact hcoreM
  have hpn : normalizer (V₁ : Set G)=H := by
    rw [normal_eq_point_centralizer d hA312 hH hU hn]
    exact le_antisymm (normalizer_le_centralizer_of_card_two _ d.flag.one_card)
      (Subgroup.centralizer_le_normalizer _)
  have hzpoint : z∈ChapterF.Section05.Source.pointRootImage c K.subtype := hpoint.symm ▸ hz
  obtain ⟨w,hw,hwz⟩ := hzpoint
  let root : P := w.val
  have hwz' : K.subtype (c.left (pi root))=z := hwz
  have hfi : Function.Injective ((K.subtype.comp c.left).comp pi) :=
    K.subtype_injective.comp (c.left_injective.comp pointInclusion_injective)
  have horder : orderOf root=2 := by
    rw [←orderOf_injective ((K.subtype.comp c.left).comp pi) hfi root]
    change orderOf (K.subtype (c.left (pi root)))=2
    rw [hwz',hoz]
  have hroot : root∈ChapterF.Section05.Source.rootSubgroup :=
    root_le_source (mem_map_of_mem (pCore 2 P).subtype hw)
  have hres : pResidual 2 G=⊤ := by
    let : IsSimpleGroup G := d.hypothesis.qtke.simple
    let : Group.IsPerfect G := by
      constructor
      rcases (inferInstance : (_root_.commutator G).Normal).eq_bot_or_eq_top with he|he
      · exact (d.hypothesis.qtke.nonabelian ((commutator_eq_bot_iff G).mp he)).elim
      · exact he
    apply (pResidual_eq_top_iff 2 G).mpr
    intro N hN hp
    let := hN
    have hs : Subsingleton (G ⧸ N) := by
      by_contra! hh
      exact Group.IsPerfect.not_isNilpotent (G ⧸ N) hp.isNilpotent
    apply eq_top_iff.mpr
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  refine ⟨c,root,?_,hl,hr,hpoint,hplane⟩
  exact {
    embedding_injective := K.subtype_injective
    root_order := horder
    root_mem := hroot
    point_normalizer := by rw [hpoint,hl]; exact hpn
    plane_normalizer := by rw [hplane,hr]; exact hnormal
    root_centralizer := by rw [hwz',hl,hcentral]
    two_residual := hres }
end CFSG.Quasithin.Chapter13.Section05.A5Source
