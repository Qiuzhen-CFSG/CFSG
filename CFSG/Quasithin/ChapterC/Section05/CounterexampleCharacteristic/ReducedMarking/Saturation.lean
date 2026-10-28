module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.Native
/-!
# Centralizer saturation on the actual reduced block

The intrinsic module centralizer is a two-group. Thus a Sylow subgroup of
its intersection with O²(KT) Baum(T) is the whole intersection. Transport
through the literal subtype map identifies it with O₂(K Baum(T)), giving
the required containment in the original Baumann subgroup.

Source: Aschbacher–Smith C.5.4, printed p.155, using B.2.18.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
theorem core_le_baumann_of_native_saturation (K T : Subgroup G) (hK : IsShort K)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hres : (pResidual 2 (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = K)
    (hsat : IsSylowSubgroupIn
      (ChapterB.baumann (P : Subgroup (K ⊔ T : Subgroup G)) ⊓
        centralizer ((U K).subgroupOf (K ⊔ T) : Set (K ⊔ T : Subgroup G)))
      ((pResidual 2 (K ⊔ T : Subgroup G) ⊔ ChapterB.baumann (P : Subgroup (K ⊔ T : Subgroup G))) ⊓
        centralizer ((U K).subgroupOf (K ⊔ T) : Set (K ⊔ T : Subgroup G)))) :
    (K ⊔ S T).pCoreIn 2 ≤ S T := by
  let A := K ⊔ T
  let B := ChapterB.baumann (P : Subgroup A)
  let C := (pResidual 2 A ⊔ B) ⊓ centralizer ((U K).subgroupOf A : Set A)
  have hCp : IsPGroup 2 C := pCore_isPGroup.to_le
    (inf_le_right.trans (reduced_module_core K T hK hT hn).le)
  obtain ⟨W,hW⟩ := hsat
  have he : (W : Subgroup C) = ⊤ := (W.is_maximal' (hCp.to_subgroup ⊤) le_top).symm
  change (W : Subgroup C).map C.subtype = B ⊓ centralizer ((U K).subgroupOf A : Set A) at hW
  rw [he,← MonoidHom.range_eq_map,range_subtype] at hW
  have hCB : C ≤ B := hW.le.trans inf_le_left
  have hB : B.map A.subtype = S T := by
    change (ChapterB.baumann (P : Subgroup A)).map A.subtype = S T
    exact (show (ChapterB.baumann (P : Subgroup A)).map A.subtype =
      ChapterB.baumann ((P : Subgroup A).map A.subtype) from
      baumann_map_injective A.subtype A.subtype_injective (P : Subgroup A)).trans
        (congrArg ChapterB.baumann hP)
  have hC : C.map A.subtype = (K ⊔ S T).pCoreIn 2 := by
    change ((pResidual 2 A ⊔ B) ⊓ centralizer ((U K).subgroupOf A : Set A)).map A.subtype = _
    rw [native_centralizer A (U K) ((map_subtype_le _).trans le_sup_left),
      map_inf _ _ _ A.subtype_injective,Subgroup.map_sup,hres,hB,subgroupOf_map_subtype]
    have hBA : K ⊔ S T ≤ A := sup_le_sup_left (show S T ≤ T from inf_le_left) K
    rw [show (K ⊔ S T) ⊓ (centralizer (U K : Set G) ⊓ A) =
      (K ⊔ S T) ⊓ centralizer (U K : Set G) by
        ext z; constructor
        · exact fun h => ⟨h.1,h.2.1⟩
        · exact fun h => ⟨h.1,h.2,hBA h.1⟩]
    exact normal_short_extension_centralizer K (S T) hK (hT.to_le inf_le_left) (inf_le_left.trans hn)
  have hcb := map_mono (f := A.subtype) hCB
  rw [hC,hB] at hcb
  exact hcb
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
