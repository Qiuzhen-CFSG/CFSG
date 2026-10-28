module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Notation
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Mathlib.GroupTheory.IndexNormal

/-!
# The characteristic-subgroup contradiction

A subgroup characteristic inside T_v is normalized by T because |T:T_v|=2.
If a proposed replacement component also normalizes it, its image in the
original ambient group lies in O₂(⟨K₁,T⟩). A nontrivial such image therefore
contradicts the first assertion of 13.6.16.

This proves the normality and core-containment step, not the construction of
the radical-supplement replacement or the strict normalizer conclusion.
Source: Aschbacher–Smith, Lemma 13.6.16(2), combined 1 March 2004 manuscript,
printed p.930.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
variable {G : Type*} [Group G]

/-- A subgroup characteristic inside C_T(v) is normal in T when that
centralizer has index two. Its image is taken in the original group G. -/
theorem characteristic_centralizer_normalized_by_sylow
    (T : Sylow 2 G) (v : G)
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (C : Subgroup (Tv (T : Subgroup G) v)) [C.Characteristic] :
    (T : Subgroup G) ≤ normalizer (C.map (Tv (T : Subgroup G) v).subtype : Set G) := by
  have hn : ((Tv (T : Subgroup G) v).subgroupOf (T : Subgroup G)).Normal :=
    normal_of_index_eq_two hidx
  have hTn := (normal_subgroupOf_iff_le_normalizer
    (show Tv (T : Subgroup G) v ≤ T from inf_le_left)).mp hn
  exact hTn.trans (normalizer_le_normalizer_characteristic_image _ C)

/-- The normal two-subgroup contradiction in the second paragraph of
13.6.16. This is used after constructing the local replacement K₁ inside
N_{K₀}(C); it does not assume that C is characteristic in G. -/
theorem characteristic_image_le_twoCore
    (T : Sylow 2 G) (v : G) (K : Subgroup G)
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (C : Subgroup (Tv (T : Subgroup G) v)) [C.Characteristic]
    (hKC : K ≤ normalizer (C.map (Tv (T : Subgroup G) v).subtype : Set G)) :
    C.map (Tv (T : Subgroup G) v).subtype ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hCT : C.map (Tv (T : Subgroup G) v).subtype ≤ T :=
    (map_subtype_le C).trans inf_le_left
  exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le hCT)
    (hCT.trans le_sup_right)
    (sup_le hKC (characteristic_centralizer_normalized_by_sylow T v hidx C))

/-- The precise application to a two-core-free replacement component:
no nontrivial characteristic subgroup of T_v is normalized by it. -/
theorem not_normalizes_characteristic_of_twoCore_eq_bot
    (T : Sylow 2 G) (v : G) (K : Subgroup G)
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (C : Subgroup (Tv (T : Subgroup G) v)) [C.Characteristic] (hC : C ≠ ⊥)
    (hcore : (K ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥) :
    ¬ K ≤ normalizer (C.map (Tv (T : Subgroup G) v).subtype : Set G) := by
  intro hKC
  have hc := characteristic_image_le_twoCore T v K hidx C hKC
  rw [hcore] at hc
  exact hC ((map_eq_bot_iff_of_injective C (Tv (T : Subgroup G) v).subtype_injective).mp
    (bot_unique hc))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
end
