module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionAmbient
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionGraphSylowModel
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionProducts
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionGraphPointCard

/-!
# Exceptional root fusion through the graph-centralizer normalizer

A strict Sylow overgroup R of Tf has a larger normalizer of Tf. If that
normalizer fixed the source root z, it would lie in the point endpoint's
graph centralizer, contradicting local Sylow maximality. Hence an element
of R normalizing Tf moves z inside its characteristic center.

The concrete eight-element center table then identifies the conjugate with
fz or ftz, using the already established graph/short fusion and root nonfusion.
A literal Q₂ conjugator exchanges fz and ftz. The resulting conjugator from
z to fz lies in R ∨ Q₂; this location is retained for the final generation
argument. The independent endpoint-Sylow and center-table inputs are explicit.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, F.4.37,
printed p.293; the resulting product fusion is used in F.5.3, p.300.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

theorem source_exists_root_moving_normalizer (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (hpoint : ∃ S : Sylow 2 (E c i false),
      (S : Subgroup (E c i false)).map (E c i false).subtype = TfImage c i)
    (R : Sylow 2 (C c i)) (hR : Tf c i < (R : Subgroup (C c i))) :
    ∃ n ∈ Rimage c i R, n ∈ normalizer (TfImage c i : Set G) ∧
      n * rootElement c i z * n⁻¹ ≠ rootElement c i z := by
  classical
  let U := (Tf c i).subgroupOf (R : Subgroup (C c i))
  have hUproper : U < ⊤ := by
    rw [lt_top_iff_ne_top,Ne,subgroupOf_eq_top]
    exact not_le_of_gt hR
  let : Group.IsNilpotent R := R.isPGroup'.isNilpotent
  obtain ⟨n,hnN,hnU⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent U hUproper)
  let j : R →* G := (C c i).subtype.comp (R : Subgroup (C c i)).subtype
  let V := (normalizer (U : Set R)).map j
  have hVnormal : V ≤ normalizer (TfImage c i : Set G) := by
    have hmap : U.map j = TfImage c i := by
      change U.map ((C c i).subtype.comp (R : Subgroup (C c i)).subtype) = _
      rw [← map_map,map_subgroupOf_eq_of_le hR.le]
      rfl
    rw [← hmap]
    exact U.le_normalizer_map j
  have hVR : V ≤ Rimage c i R := by
    rintro _ ⟨v,_,rfl⟩
    exact mem_map_of_mem (C c i).subtype v.property
  have hUV : TfImage c i ≤ V := by
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨⟨u,hR.le hu⟩,le_normalizer hu,rfl⟩
  by_contra! hnone
  have hVE : V ≤ E c i false := by
    intro v hv
    refine ⟨?_,Rimage_le_C c i R (hVR hv)⟩
    rw [← source_root_centralizer c i z h]
    exact mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (hnone v (hVR hv) (hVnormal hv)))
  obtain ⟨S,hS⟩ := hpoint
  have hp : IsPGroup 2 V := (R.isPGroup'.to_subgroup _).map j
  have hVS : V.subgroupOf (E c i false) = (S : Subgroup (E c i false)) := by
    apply S.is_maximal' hp.comap_subtype
    intro x hx
    apply hUV
    rw [← hS]
    exact mem_map_of_mem (E c i false).subtype hx
  have hVU : V = TfImage c i := by
    have he := congrArg (fun X : Subgroup (E c i false) => X.map (E c i false).subtype) hVS
    rwa [map_subgroupOf_eq_of_le hVE,hS] at he
  have hnV : j n ∈ V := mem_map_of_mem j hnN
  rw [hVU] at hnV
  obtain ⟨u,hu,he⟩ := hnV
  have he' : u = n.val := Subtype.ext he
  apply hnU
  change n.val ∈ Tf c i
  rw [← he']
  exact hu


def TfCenterImage : Subgroup G := (center (TfImage c i)).map (TfImage c i).subtype

theorem source_root_mem_TfCenterImage (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) : rootElement c i z ∈ TfCenterImage c i := by
  have hzTf : rootElement c i z ∈ TfImage c i := by
    rw [TfImage_eq]
    exact ⟨source_root_mem_sylowImage c i z h,
      mem_centralizer_singleton_iff.mpr (source_graph_commutes_root c i z h).symm.eq⟩
  apply mem_map_of_mem (TfImage c i).subtype (x := ⟨rootElement c i z,hzTf⟩)
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp ((source_root_centralizer c i z h).symm ▸
    (TfImage_le_E c i false x.property).1)

/-- The exceptional root fusion retains a conjugator in the join of the
chosen graph-centralizer Sylow and the actual plane radical. -/
theorem source_root_fuses_graph_root_of_center_table (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (hpoint : ∃ S : Sylow 2 (E c i false),
      (S : Subgroup (E c i false)).map (E c i false).subtype = TfImage c i)
    (R : Sylow 2 (C c i)) (hR : Tf c i < (R : Subgroup (C c i)))
    (hft : IsConj (Source.graphElement c i) (sourceMarkedShort c i))
    (httz : IsConj (sourceMarkedShort c i) (sourceMarkedShort c i * rootElement c i z))
    (htable : ∀ x ∈ TfCenterImage c i,
      x=1 ∨ x=rootElement c i z ∨ x=sourceMarkedShort c i ∨
      x=sourceMarkedShort c i * rootElement c i z ∨ x=Source.graphElement c i ∨
      x=Source.graphElement c i * sourceMarkedShort c i ∨
      x=Source.graphElement c i * rootElement c i z ∨
      x=Source.graphElement c i * sourceMarkedShort c i * rootElement c i z) :
    ∃ g ∈ Rimage c i R ⊔ Q c i true,
      g * rootElement c i z * g⁻¹ = Source.graphElement c i * rootElement c i z := by
  obtain ⟨n,hnR,hnN,hnmove⟩ := source_exists_root_moving_normalizer c i z h hpoint R hR
  let x := n * rootElement c i z * n⁻¹
  have hzX : IsConj (rootElement c i z) x := isConj_iff.mpr ⟨n,rfl⟩
  have hxZ : x ∈ TfCenterImage c i :=
    (mem_normalizer_iff.mp
      (normalizer_le_normalizer_characteristic_image (TfImage c i) (center (TfImage c i)) hnN)
      (rootElement c i z)).mp (source_root_mem_TfCenterImage c i z h)
  obtain ⟨q,hqQ,hqf,hqz⟩ := source_graph_short_conjugator c i z h
  have hqfz : q * (Source.graphElement c i * rootElement c i z) * q⁻¹ =
      Source.graphElement c i * sourceMarkedShort c i * rootElement c i z := by
    calc
      _ = (q * Source.graphElement c i * q⁻¹) * (q * rootElement c i z * q⁻¹) := by group
      _ = _ := by rw [hqf,mul_inv_eq_iff_eq_mul.mpr hqz.eq]
  rcases htable x hxZ with hx | hx | hx | hx | hx | hx | hx | hx
  · have hz1 := isConj_one_left.mp (hx ▸ hzX)
    have hz2 := source_root_order c i z h
    rw [hz1,orderOf_one] at hz2
    omega
  · exact False.elim (hnmove hx)
  · exact False.elim (Source.graph_not_conjugate_root c i z h
      (hft.trans (hx ▸ hzX).symm))
  · exact False.elim (Source.graph_not_conjugate_root c i z h
      ((hft.trans httz).trans (hx ▸ hzX).symm))
  · exact False.elim (Source.graph_not_conjugate_root c i z h (hx ▸ hzX).symm)
  · exact False.elim (Source.graph_not_conjugate_root c i z h
      ((isConj_iff.mpr ⟨q,hqf⟩).trans (hx ▸ hzX).symm))
  · exact ⟨n,mem_sup_left hnR,hx⟩
  · refine ⟨q⁻¹*n,(Rimage c i R ⊔ Q c i true).mul_mem
      (mem_sup_right ((Q c i true).inv_mem hqQ)) (mem_sup_left hnR),?_⟩
    calc
      _ = q⁻¹ * (n * rootElement c i z * n⁻¹) * q := by group
      _ = q⁻¹ * (q * (Source.graphElement c i * rootElement c i z) * q⁻¹) * q := by
        rw [show n * rootElement c i z * n⁻¹ =
          Source.graphElement c i * sourceMarkedShort c i * rootElement c i z from hx,←hqfz]
      _ = _ := by group


/-- The actual source point-endpoint calculation discharges the local Sylow
premise of the root-moving normalizer argument. -/
theorem source_root_moving_normalizer (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (R : Sylow 2 (C c i)) (hR : Tf c i < (R : Subgroup (C c i))) :
    ∃ n ∈ Rimage c i R, n ∈ normalizer (TfImage c i : Set G) ∧
      n * rootElement c i z * n⁻¹ ≠ rootElement c i z :=
  source_exists_root_moving_normalizer c i z h
    (source_Tf_sylow_point c i h.embedding_injective) R hR

/-- Original-source root fusion with only the earlier fusion and concrete
center table remaining; the endpoint Sylow premise is discharged. -/
theorem source_root_fusion_conjugator_of_center_table (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (R : Sylow 2 (C c i)) (hR : Tf c i < (R : Subgroup (C c i)))
    (hft : IsConj (Source.graphElement c i) (sourceMarkedShort c i))
    (httz : IsConj (sourceMarkedShort c i) (sourceMarkedShort c i * rootElement c i z))
    (htable : ∀ x ∈ TfCenterImage c i,
      x=1 ∨ x=rootElement c i z ∨ x=sourceMarkedShort c i ∨
      x=sourceMarkedShort c i * rootElement c i z ∨ x=Source.graphElement c i ∨
      x=Source.graphElement c i * sourceMarkedShort c i ∨
      x=Source.graphElement c i * rootElement c i z ∨
      x=Source.graphElement c i * sourceMarkedShort c i * rootElement c i z) :
    ∃ g ∈ Rimage c i R ⊔ Q c i true,
      g * rootElement c i z * g⁻¹ = Source.graphElement c i * rootElement c i z :=
  source_root_fuses_graph_root_of_center_table c i z h
    (source_Tf_sylow_point c i h.embedding_injective) R hR hft httz htable

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
