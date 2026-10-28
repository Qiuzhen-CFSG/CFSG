module
public import CFSG.Quasithin.Chapter3.Section01.BaumannSylow.SpanSetup
public import CFSG.Quasithin.ChapterB.Section02.Baumann.SpanSylow
public import CFSG.Quasithin.Chapter3.Section01.E23Input

/-!
# From the actual Baumann span to the original residual Sylow

Both normalizer cases of Hypothesis 3.1.5 give a subgroup normalized by
H∩M in which R=O₂(M₀) is Sylow. The source Sylow extension in the
Baum(T)-conjugate span lies there. Baumann weak closure then gives
R Sylow in O²(H)R, retaining all intrinsic-to-ambient maps.

Source: Aschbacher–Smith 3.1.7, printed pp.575–576; this is the
placement argument for the natural S₅ branch of E.2.3.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter3
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.residual_sylow_of_baumann_span
    (h : QrcHypotheses T M M₀ H V)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (Q : Subgroup H)
    (hQ : Chapter1.IsSylowIn 2 Q
      (pResidual 2 H ⊔ ChapterB.baumann ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H)))
    (hBQ : ChapterB.baumann ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H) ≤ Q)
    (hspan : Q ≤ conjugateSpanBy
      (ChapterB.baumann ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H))
      (pResidual 2 H ⊓ ChapterB.minimalParabolicMax (T.subtype h.right_mem.1.1.2) hP)) :
    Chapter1.IsSylowIn 2 (M₀.pCoreIn 2) ((pResidual 2 H).map H.subtype ⊔ M₀.pCoreIn 2) := by
  obtain ⟨D,hn,hR⟩ := h.exists_normal_sylow_container_in_right
  let S := T.subtype h.right_mem.1.1.2
  let R := (M₀.pCoreIn 2).subgroupOf H
  have hRT : M₀.pCoreIn 2 ≤ (T : Subgroup G) := by rw [h.core_eq_centralizer]; exact inf_le_left
  have hRS : R ≤ S := fun x hx => hRT hx
  have hbmap : (ChapterB.baumann (S : Subgroup H)).map H.subtype = ChapterB.baumann (T : Subgroup G) := by
    have he := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
    change (ChapterB.baumann (S : Subgroup H)).map H.subtype = ChapterB.baumann ((S : Subgroup H).map H.subtype) at he
    have hm : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le h.right_mem.1.1.2
    exact he.trans (congrArg ChapterB.baumann hm)
  have hBR : ChapterB.baumann (S : Subgroup H) ≤ R := by
    intro x hx
    exact (h.baumann_core hJ).2 (hbmap ▸ mem_map_of_mem H.subtype hx)
  have hn' : pResidual 2 H ⊓ ChapterB.minimalParabolicMax S hP ≤ normalizer (D : Set H) := by
    rw [h.intrinsic_maximal_eq_intersection hP]
    exact inf_le_right.trans hn
  have hs := ChapterB.sylow_sup_of_baumann_span S (pResidual 2 H) D R
    (pResidual 2 H ⊓ ChapterB.minimalParabolicMax S hP) Q hRS hBR hR hn' hQ hBQ hspan
  have hm := (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mpr hs
  rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le (hRT.trans h.right_mem.1.1.2)] at hm
end CFSG.Quasithin.Chapter3
