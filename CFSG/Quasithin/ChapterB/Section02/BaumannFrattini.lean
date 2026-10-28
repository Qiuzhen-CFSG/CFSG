module
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.GroupTheory.NormalClosureCentralizerCore
public import Theory.GroupTheory.SylowNormalIntersection
public import Stellmacher.BaumannNormalizer
public import Theory.GroupTheory.CharacteristicNormalizerClosure
/-!
# Characteristic Baumann subgroups in the centralizing Frattini case

When Baum(T) equals Baum(T ∩ N) for a normal subgroup N of an
intermediate overgroup M, the Frattini argument for the actual Sylow
intersection gives M = N N_M(C) for every characteristic subgroup C
of Baum(T). In particular this applies to N = C_M(V) whenever J(T)
centralizes the elementary normal module V, by source 14.1.2(1).

This proves the centralizing branch of source 14.1.11 for the original
characteristic subgroup, without maximality, a control assumption, or
any hypothesis on the other characteristic subgroups of T.
Source: Aschbacher–Smith, combined manuscript (1 March 2004),
14.1.2(1) and 14.1.11, printed pp.975–978.
-/

public section
open Subgroup Stellmacher CFSG.Quasithin.ChapterB
namespace CFSG.Quasithin.ChapterB.BaumannFrattini
variable {G : Type*} [Group G] [Finite G]

theorem baumann_characteristic_frattini (T : Sylow 2 G) (M N : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hNM : N ≤ M) [(N.subgroupOf M).Normal]
    (hB : baumann (T : Subgroup G) = baumann ((T : Subgroup G) ⊓ N))
    (C : Subgroup (baumann (T : Subgroup G))) [C.Characteristic] :
    M = N ⊔ (M ⊓ normalizer (C.map (baumann (T : Subgroup G)).subtype : Set G)) := by
  let S := T.subtype hTM
  let K := N.subgroupOf M
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal K
  have hPK : ((P : Subgroup K).map K.subtype).map M.subtype =
      (T : Subgroup G) ⊓ N := by
    rw [hP,subgroupOf_map_subtype,Subgroup.map_inf _ _ M.subtype M.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM,map_subgroupOf_eq_of_le hNM]
  have hn : (normalizer ((P : Subgroup K).map K.subtype : Set M)).map M.subtype ≤
      normalizer (C.map (baumann (T : Subgroup G)).subtype : Set G) := by
    have h := ((P : Subgroup K).map K.subtype).le_normalizer_map M.subtype
    rw [hPK] at h
    refine h.trans ((normalizer_le_normalizer_baumann _).trans ?_)
    change normalizer (baumann ((T : Subgroup G) ⊓ N) : Set G) ≤ _
    rw [← hB]
    exact normalizer_le_normalizer_characteristic_image _ C
  have hf := congrArg (map M.subtype) P.normalizer_sup_eq_top
  rw [Subgroup.map_sup,← MonoidHom.range_eq_map,range_subtype,
    map_subgroupOf_eq_of_le hNM] at hf
  apply le_antisymm
  · exact hf.symm.le.trans (sup_le (le_sup_of_le_right (le_inf (map_subtype_le _) hn)) le_sup_left)
  · exact sup_le hNM inf_le_left

theorem centralizing_characteristic_factorization (T : Sylow 2 G) (M V : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M)
    [IsElementaryAbelian 2 V] [(V.subgroupOf M).Normal]
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ M ⊓ centralizer (V : Set G))
    (C : Subgroup (baumann (T : Subgroup G))) [C.Characteristic] :
    M = (M ⊓ centralizer (V : Set G)) ⊔
      (M ⊓ normalizer (C.map (baumann (T : Subgroup G)).subtype : Set G)) := by
  have hVT : V ≤ (T : Subgroup G) := by
    have hp : IsPGroup 2 (V.subgroupOf M) :=
      (IsElementaryAbelian.isPGroup 2 V).of_equiv (subgroupOfEquivOfLe hVM).symm
    have hle := hp.le_sylow_of_normal (T.subtype hTM)
    intro v hv
    exact hle (show (⟨v,hVM hv⟩ : M) ∈ V.subgroupOf M from hv)
  have hB := lemma_B_2_3_5 (T : Subgroup G) V hVT (hJ.trans inf_le_right)
  have hTMV : (T : Subgroup G) ⊓ (M ⊓ centralizer (V : Set G)) =
      (T : Subgroup G) ⊓ centralizer (V : Set G) := by
    rw [← inf_assoc,inf_eq_left.mpr hTM]
  have hn : ((M ⊓ centralizer (V : Set G)).subgroupOf M).Normal := by
    have he : (M ⊓ centralizer (V : Set G)).subgroupOf M =
        centralizer (V.subgroupOf M : Set M) := by
      apply map_injective M.subtype_injective
      rw [map_subgroupOf_eq_of_le inf_le_left,map_centralizer_subtype,
        map_subgroupOf_eq_of_le hVM]
    rw [he]
    infer_instance
  exact baumann_characteristic_frattini T M _ hTM inf_le_left (by rw [hTMV]; exact hB) C
end CFSG.Quasithin.ChapterB.BaumannFrattini
