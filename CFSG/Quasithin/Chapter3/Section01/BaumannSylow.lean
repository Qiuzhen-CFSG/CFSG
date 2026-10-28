module
public import CFSG.Quasithin.Chapter3.Section01.Configuration
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.BaumannMap
public import Theory.GroupTheory.SylowNormalizedEnlargement
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# Baumann heredity and the linear residual-Sylow branch

The original reduced module lies in O₂(M₀), hence in T. If J(T)
centralizes it, B.2.3(5) identifies Baum(T) with Baum(O₂(M₀)).
The exact intrinsic Sylow conclusion of E.2.3(2) then transports to G
and enlarges to O₂(M₀) in O²(H)O₂(M₀).

The E.2.3 Sylow statement remains the explicit earlier-source input;
no alternating-five branch is inferred from it.
Source: Aschbacher–Smith, Lemma 3.1.7, printed pp.575–576.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter3
open Stellmacher
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

omit [Finite G] in
theorem QrcHypotheses.module_le_sylow
    (h : QrcHypotheses T M M₀ H V) : V ≤ (T : Subgroup G) := by
  let := h.module_elementary
  have hvR : V ≤ M₀.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 V) h.module_le h.module_normalized
  rw [h.core_eq_centralizer] at hvR
  exact hvR.trans inf_le_left

theorem QrcHypotheses.baumann_core
    (h : QrcHypotheses T M M₀ H V)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    ChapterB.baumann (T : Subgroup G) = ChapterB.baumann (M₀.pCoreIn 2) ∧
      ChapterB.baumann (T : Subgroup G) ≤ M₀.pCoreIn 2 := by
  let := h.module_elementary
  have he := ChapterB.lemma_B_2_3_5 (T : Subgroup G) V h.module_le_sylow hJ
  rw [← h.core_eq_centralizer] at he
  exact ⟨he, he ▸ inf_le_left⟩

theorem QrcHypotheses.residual_sylow_of_baumann_sylow
    (h : QrcHypotheses T M M₀ H V)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hs : Chapter1.IsSylowIn 2 (ChapterB.baumann
        ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H))
      (pResidual 2 H ⊔ ChapterB.baumann
        ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H))) :
    Chapter1.IsSylowIn 2 (M₀.pCoreIn 2)
      ((pResidual 2 H).map H.subtype ⊔ M₀.pCoreIn 2) := by
  let S := ChapterB.baumann (T : Subgroup G)
  have hbmap : (ChapterB.baumann
      ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H)).map H.subtype = S := by
    have hTm : ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H).map H.subtype =
        (T : Subgroup G) := map_subgroupOf_eq_of_le h.right_mem.1.1.2
    have hm := baumann_map_injective H.subtype H.subtype_injective
      ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H)
    change (ChapterB.baumann _).map H.subtype = ChapterB.baumann _ at hm
    exact hm.trans (congrArg ChapterB.baumann hTm)
  have hsm := (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mpr hs
  rw [Subgroup.map_sup, hbmap] at hsm
  obtain ⟨P, hP⟩ := hsm
  have hRT : M₀.pCoreIn 2 ≤ (T : Subgroup G) := by
    rw [h.core_eq_centralizer]
    exact inf_le_left
  have hn : M₀.pCoreIn 2 ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) := by
    have hN := (pResidual 2 H).le_normalizer_map H.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hN
    exact (hRT.trans h.right_mem.1.1.2).trans hN
  exact (isPGroup_pCoreIn 2 M₀).exists_sylow_sup_of_smaller_sylow _ S _
    (h.baumann_core hJ).2 hn P hP
end CFSG.Quasithin.Chapter3
