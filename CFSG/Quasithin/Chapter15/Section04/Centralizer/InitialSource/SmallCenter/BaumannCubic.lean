module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.BaumannKernel
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.CubicBlock
public import Stellmacher.BaumannTwoOvergroupTransport
public import Stellmacher.BaumannMap

/-!
# Thompson geometry of the selected Baumann cubic block

The original Baumann group is itself Baumann fixed. The selected local
class has its actual kernel O₂(K), so the cubic local-class theorem supplies
the Thompson commutator and module support. Minimal-parabolic normal
generation also puts K in the original normal closure of Baum(T).

Source: Aschbacher--Smith C.1.26--28 and 15.4.7, pp.132--134,1158.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
open ChapterC.GlaubermanNiles
variable {G : Type*} [Group G] [Finite G]

/-- The original Baumann subgroup is fixed by the intrinsic Baumann construction. -/
theorem baumann_isBaumannFixed (T : Sylow 2 G) :
    IsBaumannFixed (ChapterB.baumann (T : Subgroup G)) := by
  let B := ChapterB.baumann (T : Subgroup G)
  apply map_injective B.subtype_injective
  change (ChapterB.baumann (⊤ : Subgroup B)).map B.subtype = (⊤ : Subgroup B).map B.subtype
  unfold ChapterB.baumann ChapterB.thompsonAlpha
  rw [baumann_map_injective B.subtype B.subtype_injective]
  have hm : (⊤ : Subgroup B).map B.subtype = B := by rw [←MonoidHom.range_eq_map,range_subtype]
  rw [hm]
  exact baumann_eq_of_intermediate (T : Subgroup G) B le_rfl inf_le_left

/-- The local cubic block retains its actual normal-closure placement, action and support. -/
theorem selected_cubic_geometry (T : Sylow 2 G) (K : Subgroup G)
    (hBK : ChapterB.baumann (T : Subgroup G) ≤ K)
    (hclass : InLocalClass (inclusion hBK))
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hb : ChapterC.IsBlock (pResidual 2 K))
    (ha : ChapterC.IsAlternatingBlock (pResidual 2 K) 3) :
    K ≤ normalClosure (ChapterB.baumann (T : Subgroup G) : Set G) ∧
    (pResidual 2 K).map K.subtype =
      ⁅(pResidual 2 K).map K.subtype,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
    ((ChapterC.blockU (pResidual 2 K)).map (pResidual 2 K).subtype).map K.subtype ≤
      (localV (inclusion hBK)).map K.subtype := by
  let B := ChapterB.baumann (T : Subgroup G)
  obtain ⟨P,he,hP⟩ := hclass.sylow
  have hPB : (P : Subgroup K).map K.subtype = B := by
    rw [←he,MonoidHom.range_eq_map,map_map]
    change (⊤ : Subgroup B).map B.subtype = B
    rw [←MonoidHom.range_eq_map,range_subtype]
  have hk := selected_localKernel T K P hPB hC
  have hJ := hclass.cubic_residual_thompson (baumann_isBaumannFixed T) hk hb ha P he
  have hJB : (elementaryAbelianMaxJ (P : Subgroup K)).map K.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective K.subtype K.subtype_injective,hPB]
    exact (twoSubgroup_thompson_baumann_eq T B (T.isPGroup'.to_le inf_le_left) le_rfl).1
  refine ⟨?_,?_,map_mono (hclass.cubic_block_support hk hb ha)⟩
  · let L := normalClosure (B : Set G)
    let : L.Normal := normalClosure_normal
    have hPN : (P : Subgroup K) ≤ L.subgroupOf K := by
      intro p hp
      exact le_normalClosure (hPB ▸ mem_map_of_mem K.subtype hp)
    have hN := P.normal_eq_top_of_uniqueMaximal hP.1
      ((ChapterB.isMinimalParabolicOver_top_iff P).mp hP).2 (L.subgroupOf K) hPN
    intro k hk
    have hkN : (⟨k,hk⟩ : K) ∈ L.subgroupOf K := by rw [hN]; exact mem_top _
    exact hkN
  · have hh := congrArg (map K.subtype) hJ
    rwa [map_commutator,hJB] at hh
end CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
