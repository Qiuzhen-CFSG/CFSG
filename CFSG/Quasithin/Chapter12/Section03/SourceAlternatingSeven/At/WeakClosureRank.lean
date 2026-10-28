module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.WeakClosureRank
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.Intersections

/-!
# WeakClosureRank at the original ambient group and Sylow subgroup

These are the same source arguments as `WeakClosureRank`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 ChapterE BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable (S : Setup T L V) (D : S.LocalAnalysis)

variable (structural : Structural1222At KnownSimple.IsKnownSimple T)

include S D structural

theorem weight_four_of_escaping_centralizer_at {U : Subgroup G} (hUV : U ≤ V)
    (hesc : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    D.model.WeightFour U := by
  obtain ⟨g, hg, hgN⟩ := SetLike.not_le_iff_exists.mp hesc
  intro v hv hv1
  have hvG : (v : G) ≠ 1 := fun he => hv1 (Subtype.ext he)
  apply intersection_weight_four_at S D structural hgN (x := (v : G)) ?_ hvG
  refine ⟨v.property, ?_⟩
  refine ⟨v, hUV hv, ?_⟩
  change g * v.val * g⁻¹ = v.val
  exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hg) _ hv).symm

theorem escaping_subgroup_rank_le_three_at {U : Subgroup G} (hUV : U ≤ V)
    (hesc : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    Nat.log 2 (Nat.card U) ≤ 3 :=
  D.model.log_card_le_three_of_weight_four hUV
    (weight_four_of_escaping_centralizer_at S D structural hUV hesc)

theorem globalR_ge_three_at : (3 : ℕ∞) ≤ globalR V := by
  let _ := S.chosen.elementary
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨hUV, hesc⟩
  have hb := escaping_subgroup_rank_le_three_at S D structural hUV hesc
  have hr : 3 ≤ subgroupCorank V U := by
    rw [subgroupCorank, ← log_card_sub_log_card_eq_log_relIndex V U hUV,
      D.model.log_card_eq_six]
    omega
  exact_mod_cast hr

theorem one_lt_globalR_at : (1 : ℕ∞) < globalR V :=
  lt_of_lt_of_le (by decide : (1 : ℕ∞) < 3) (globalR_ge_three_at S D structural)

theorem centralizer_normalizes_of_corank_le_two_at {U : Subgroup G} (hUV : U ≤ V)
    (hr : subgroupCorank V U ≤ 2) :
    centralizer (U : Set G) ≤ normalizer (V : Set G) := by
  apply centralizer_le_normalizer_of_corank_lt_globalR hUV
  apply lt_of_lt_of_le _ (globalR_ge_three_at S D structural)
  exact_mod_cast (show subgroupCorank V U < 3 by omega)

theorem conjugate_centralizer_normalizes_of_corank_le_two_at (g : G)
    {U : Subgroup G} (hUV : U ≤ V.map (MulAut.conj g).toMonoidHom)
    (hr : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) U ≤ 2) :
    centralizer (U : Set G) ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  apply centralizer_le_normalizer_of_corank_lt_globalR hUV
  rw [globalR_map_equiv]
  apply lt_of_lt_of_le _ (globalR_ge_three_at S D structural)
  exact_mod_cast (show subgroupCorank (V.map (MulAut.conj g).toMonoidHom) U < 3 by omega)

theorem conjugate_centralizer_rank_le_three_at (g : G)
    (hn : ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    Nat.log 2 (Nat.card (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G) :
      Subgroup G)) ≤ 3 := by
  let _ := S.chosen.elementary
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hb := (globalR_ge_three_at S D structural).trans
    (globalR_le_conjugate_centralizer_corank g hn)
  have hb' : 3 ≤ subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G)) := by exact_mod_cast hb
  rw [subgroupCorank, ← log_card_sub_log_card_eq_log_relIndex _ _ inf_le_left,
    card_map_of_injective (MulAut.conj g).injective, D.model.log_card_eq_six] at hb'
  omega

theorem local_rank_three_centralizer_at {U : Subgroup G} (hUV : U ≤ V)
    (hw : D.model.WeightFour U) (hr : Nat.log 2 (Nat.card U) = 3) :
    normalizer (L : Set G) ⊓ centralizer (U : Set G) =
      normalizer (L : Set G) ⊓ centralizer (V : Set G) := by
  have hUne : U ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hr
    norm_num at hr
  apply le_antisymm
  · apply le_inf inf_le_left
    have hTI := inf_centralizer_le_normalizer_of_trivial_intersections
      (S.hypothesis.source_chosen_TI_at structural S.chosen) hUne hUV
    exact (le_inf hTI inf_le_right).trans
      (D.model.normalizer_inf_centralizer_of_weight_four_rank_three hUV hw hr).le
  · exact inf_le_inf_left _ (centralizer_le hUV)

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

