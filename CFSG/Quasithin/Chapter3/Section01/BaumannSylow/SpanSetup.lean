module
public import CFSG.Quasithin.Chapter3.Section01.BaumannSylow
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.NormalizerAction
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# A normal Sylow container in the original qrc normalizer

In case I of Hypothesis 3.1.5, A.4.2 makes O₂(M₀) Sylow in the
centralizer of O²(M₀)/O₂(O²(M₀)); that centralizer is normalized by
H∩M. In case II, intersect C_G(V) with H∩M and restrict the original
Sylow subgroup. Both cases give a literal intrinsic H-subgroup D with
R Sylow and H∩M normalizing D. The intrinsic minimal parabolic maximal
subgroup is identified with this same intersection H∩M.

These supply the S₅ conjugate-span placement step of 3.1.7 without
assuming R normal in H∩M. Source: Aschbacher–Smith pp.574–576.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter3
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M M₀ H V : Subgroup G}

private theorem normal_sylow_intersection (N B : Subgroup G)
    (hNB : N ≤ B) (hBN : B ≤ normalizer (N : Set G)) (S : Sylow 2 B) :
    Chapter1.IsSylowIn 2 ((S : Subgroup B).map B.subtype ⊓ N) N := by
  let : (N.subgroupOf B).Normal := normal_subgroupOf_of_le_normalizer hBN
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal (N.subgroupOf B)
  let e := subgroupOfEquivOfLe hNB
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((P : Subgroup (N.subgroupOf B)).map e.toMonoidHom).map N.subtype = _
  rw [map_map]
  change (P : Subgroup (N.subgroupOf B)).map (B.subtype.comp (N.subgroupOf B).subtype) = _
  rw [← map_map,hP,subgroupOf_map_subtype, map_inf _ _ _ B.subtype_injective,
    map_subgroupOf_eq_of_le hNB]

theorem QrcHypotheses.exists_normal_sylow_container
    (h : QrcHypotheses T M M₀ H V) :
    ∃ D : Subgroup G, H ⊓ M ≤ normalizer (D : Set G) ∧
      Chapter1.IsSylowIn 2 (M₀.pCoreIn 2) D := by
  have hTM : (T : Subgroup G) ≤ M := h.sylow_le.trans h.left_le
  rcases h.normalizer_cases with hn | hn
  · let L := (pResidual 2 M₀).map M₀.subtype
    have hTL : (T : Subgroup G) ≤ normalizer (L : Set G) := by
      have hh := (pResidual 2 M₀).le_normalizer_map M₀.subtype
      rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hh
      exact h.sylow_le.trans hh
    have hp : IsPPerfect 2 L := (isPPerfect_pResidual 2).of_surjective
      ((M₀.subtype).subgroupMap (pResidual 2 M₀))
      (M₀.subtype.subgroupMap_surjective (pResidual 2 M₀))
    have hLM : L ⊔ (T : Subgroup G) = M₀ := by
      have he := congrArg (map M₀.subtype) (pResidual_sup_sylow_eq_top (T.subtype h.sylow_le))
      have hmap : ((T.subtype h.sylow_le : Sylow 2 M₀) : Subgroup M₀).map M₀.subtype = T :=
        map_subgroupOf_eq_of_le h.sylow_le
      rw [Subgroup.map_sup,hmap,
        ← MonoidHom.range_eq_map,range_subtype] at he
      exact he
    let D := ChapterA.Section04.twoSectionCentralizer L (normalizer (L : Set G))
    refine ⟨D,hn.trans (ChapterA.Section04.twoSectionCentralizer_normalized L _ le_rfl),?_⟩
    obtain ⟨P,hP⟩ := ChapterA.Section04.sylow_core_sectionCentralizer T L hp hTL
    rw [hLM] at hP
    exact ⟨P,hP⟩
  · let B := H ⊓ M
    let D := B ⊓ centralizer (V : Set G)
    have hBD : B ≤ normalizer (D : Set G) :=
      (le_inf B.le_normalizer (hn.trans (normalizer_le_normalizer_centralizer V))).trans
        inf_normalizer_le_normalizer_inf
    let S := T.subtype (le_inf h.right_mem.1.1.2 hTM)
    have hSm : (S : Subgroup B).map B.subtype = T :=
      map_subgroupOf_eq_of_le (le_inf h.right_mem.1.1.2 hTM)
    have hR : (T : Subgroup G) ⊓ D = M₀.pCoreIn 2 := by
      rw [h.core_eq_centralizer]
      apply le_antisymm
      · exact inf_le_inf_left _ inf_le_right
      · exact le_inf inf_le_left (le_inf (inf_le_left.trans (le_inf h.right_mem.1.1.2 hTM)) inf_le_right)
    refine ⟨D,hBD,?_⟩
    have he := normal_sylow_intersection D B inf_le_left hBD S
    rwa [hSm,hR] at he
end CFSG.Quasithin.Chapter3

namespace CFSG.Quasithin.Chapter3
open ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M M₀ H V : Subgroup G}

omit [Finite G] in
theorem QrcHypotheses.intrinsic_maximal_eq_intersection
    (h : QrcHypotheses T M M₀ H V)
    (hP : IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤) :
    minimalParabolicMax (T.subtype h.right_mem.1.1.2) hP = (H ⊓ M).subgroupOf H := by
  let S := T.subtype h.right_mem.1.1.2
  have hi := HStar.unique_maximal T (h.sylow_le.trans h.left_le) h.right_mem
  have hs : (S : Subgroup H) ≤ (H ⊓ M).subgroupOf H := by
    intro x hx
    exact ⟨h.right_mem.1.1.2 hx,(h.sylow_le.trans h.left_le) hx⟩
  have hBne : (H ⊓ M).subgroupOf H ≠ ⊤ := by
    intro he
    have hm := congrArg (map H.subtype) he
    rw [map_subgroupOf_eq_of_le inf_le_left, ← MonoidHom.range_eq_map,range_subtype] at hm
    exact hi.2.1.lt.ne hm
  have hcoat : IsCoatom ((H ⊓ M).subgroupOf H) := by
    refine ⟨hBne,?_⟩
    intro Y hY
    have hy : H ⊓ M < Y.map H.subtype := by
      rw [← map_subgroupOf_eq_of_le (show H ⊓ M ≤ H from inf_le_left)]
      exact (map_lt_map_iff_of_injective H.subtype_injective).mpr hY
    have he := (hi.2.1.eq_or_eq hy.le (map_subtype_le Y)).resolve_left hy.ne'
    apply map_injective H.subtype_injective
    rw [he, ← MonoidHom.range_eq_map,range_subtype]
  exact (minimalParabolicMax_unique S hP hcoat hs).symm
end CFSG.Quasithin.Chapter3

namespace CFSG.Quasithin.Chapter3
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.exists_normal_sylow_container_in_right
    (h : QrcHypotheses T M M₀ H V) :
    ∃ D : Subgroup H,
      ((H ⊓ M).subgroupOf H) ≤ normalizer (D : Set H) ∧
      Chapter1.IsSylowIn 2 ((M₀.pCoreIn 2).subgroupOf H) D := by
  obtain ⟨D,hn,hR⟩ := h.exists_normal_sylow_container
  let D' := D ⊓ H
  have hRT : M₀.pCoreIn 2 ≤ (T : Subgroup G) := by
    rw [h.core_eq_centralizer]
    exact inf_le_left
  have hRD : M₀.pCoreIn 2 ≤ D' :=
    le_inf (Chapter1.isSylowIn_iff.mp hR).2.1 (hRT.trans h.right_mem.1.1.2)
  have hr := hR.restrict hRD (inf_le_left : D' ≤ D)
  have hn' : H ⊓ M ≤ normalizer (D' : Set G) :=
    (le_inf hn (inf_le_left.trans H.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  refine ⟨D'.subgroupOf H,?_ ,?_⟩
  · apply le_trans _ (le_normalizer_comap H.subtype)
    exact subgroupOf_mono H hn'
  · apply (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le (hRT.trans h.right_mem.1.1.2),map_subgroupOf_eq_of_le inf_le_right]
    exact hr
end CFSG.Quasithin.Chapter3
