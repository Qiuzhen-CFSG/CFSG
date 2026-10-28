module
public import CFSG.Quasithin.Chapter14.Section02.UnitaryKOne
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# The original normal Bender Borel

The normalizer of T intersection K contains T and is proper, because the
rank-one Sylow normalizer in K is proper. Minimal-parabolic uniqueness
puts it in the original maximal overgroup. Rank-one maximality gives the
reverse inclusion for that overgroup intersected with K.

Source: Aschbacher--Smith 14.2.11 and the paragraph following 14.2.14,
printed pp.983--984.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterB ChapterF.Source
variable {H : Type*} [Group H] [Finite H]

theorem normal_bender_borel_eq_overlap
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hq : IsRankOneModel (K ⧸ pCore 2 K)) :
    borel K (T : Subgroup H) = minimalParabolicMax T hP ⊓ K := by
  obtain ⟨P,hPmap⟩ := T.exists_sylow_map_eq_inf_of_normal K
  have hf := rankOneBorelFacts_of_sylow K (T : Subgroup H) P hPmap
    (rankOneSylowFacts_of_rankOneQuotient hq P)
  let N := normalizer (((T : Subgroup H) ⊓ K : Subgroup H) : Set H)
  have hTN : (T : Subgroup H) ≤ N := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    exact ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht),
      (inferInstance : K.Normal).conj_mem x hx.2 t⟩
  have hN : N < ⊤ := lt_top_iff_ne_top.mpr (by
    intro hn
    have hb : borel K (T : Subgroup H) = K := by
      change K ⊓ N = K
      rw [hn,inf_top_eq]
    exact hf.proper.ne hb)
  have hNM : N ≤ minimalParabolicMax T hP :=
    hP.1.le_maximal ⟨(minimalParabolicMax_spec T hP).2,
      (minimalParabolicMax_spec T hP).1.covBy_top⟩ hTN hN
  apply le_antisymm
  · exact le_inf (inf_le_right.trans hNM) inf_le_left
  · apply hf.unique_maximal
    · exact le_inf (inf_le_left.trans (minimalParabolicMax_spec T hP).2) inf_le_right
    · apply lt_of_le_of_ne inf_le_right
      intro he
      have hKM : K ≤ minimalParabolicMax T hP := he.symm ▸ inf_le_left
      exact (minimalParabolicMax_spec T hP).1.ne_top
        (top_unique (hgen ▸ sup_le hKM (minimalParabolicMax_spec T hP).2))
end CFSG.Quasithin.Chapter14.Section02
