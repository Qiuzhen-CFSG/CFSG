module

public import CFSG.Quasithin.Chapter13.Section07.PairGeneration
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.Kernel
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# The fixed-line contradiction at the end of13.7.16

The actual paired spans, O₂(H), and Q generate LT. A vector of U₀∩U_H^g
fixed by T is therefore fixed by LT. A nontrivial T-normalized subgroup of
U₀ meets Z(T), so it cannot simultaneously have trivial L₁-centralizer
and have all its T-fixed elements in U_H^g.

The final consumer uses W=[U₀,K] for the original normal component. The
two displayed fixed-space conditions are the precise remaining natural
L₃(2) module calculations from13.5.2(3) and the preceding part of13.7.16;
component classification and those calculations are not asserted here.
Source: Aschbacher–Smith13.7.16(2), last paragraph, printed p.944.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The original common fixed vectors of the pair centralize LT. -/
theorem pair_sylow_fixed_centralizes_local
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,H.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃) :
    ((Section08.Source.UH H V₃ ⊓ centralizer (H.pCoreIn 2 : Set G)) ⊓
      conjugate (Section08.Source.UH H V₃) (g : G)) ⊓ centralizer (T : Set G) ≤
        centralizer ((L ⊔ (T : Subgroup G) : Subgroup G) : Set G) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let U₀ := F.UH ⊓ centralizer (F.QH : Set G)
  let Ug := conjugate F.UH (g : G)
  let Z := (U₀ ⊓ Ug) ⊓ centralizer (T : Set G)
  have hVU : F.VH ≤ centralizer (F.UH : Set G) := (VH_centralizes_UH d h hU).trans inf_le_right
  have hgVU : conjugate F.VH (g : G) ≤ centralizer (Ug : Set G) :=
    (map_mono (f := (MulAut.conj (g : G)⁻¹).toMonoidHom) hVU).trans
      (map_centralizer_le_centralizer_image (F.UH : Set G) (MulAut.conj (g : G)⁻¹).toMonoidHom)
  apply le_centralizer_iff.mpr
  apply (pair_core_generate d h hU hV hne g hout).ge.trans
  apply sup_le
  · apply sup_le
    · exact sup_le
        (hVU.trans (centralizer_le (show Z ≤ F.UH from inf_le_left.trans (inf_le_left.trans inf_le_left))))
        (hgVU.trans (centralizer_le (show Z ≤ Ug from inf_le_left.trans inf_le_right)))
    · exact le_centralizer_iff.mp (show Z ≤ centralizer (F.QH : Set G) from
        inf_le_left.trans (inf_le_left.trans inf_le_right))
  · have hQT : (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 ≤ (T : Subgroup G) :=
      h.sylow_centralizer.symm.le.trans inf_le_left
    exact hQT.trans (le_centralizer_iff.mp (show Z ≤ centralizer (T : Set G) from inf_le_right))

/-- The literal fixed-line contradiction: a nonzero T-normalized part of U₀
cannot satisfy both natural-module fixed-space conditions. -/
theorem pair_normal_fixed_layer_eq_bot
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,H.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    (W : Subgroup G)
    (hWU : W ≤ Section08.Source.UH H V₃ ⊓ centralizer (H.pCoreIn 2 : Set G))
    (hTW : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hfixed : W ⊓ centralizer
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ : Set G) = ⊥)
    (hopp : W ⊓ centralizer (T : Set G) ≤ conjugate (Section08.Source.UH H V₃) (g : G)) :
    W = ⊥ := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  have hWT : W ≤ (T : Subgroup G) := (hWU.trans inf_le_left).trans (h.UH_le_QH.trans h.QH_le_T)
  let : (W.subgroupOf (T : Subgroup G)).Normal := normal_subgroupOf_of_le_normalizer hTW
  by_contra hW
  have hW' : W.subgroupOf (T : Subgroup G) ≠ ⊥ := by
    intro he
    have hm := congrArg (map (T : Subgroup G).subtype) he
    rw [map_subgroupOf_eq_of_le hWT,Subgroup.map_bot] at hm
    exact hW hm
  have hmeet := center_inf_ne_bot_of_normal T.isPGroup' (W.subgroupOf (T : Subgroup G)) hW'
  obtain ⟨x,hx⟩ := ne_bot_iff_exists_ne_one.mp hmeet
  have hxW : ((x : (T : Subgroup G)) : G) ∈ W := x.property.2
  have hxT : ((x : (T : Subgroup G)) : G) ∈ centralizer (T : Set G) := by
    intro t ht
    exact congrArg Subtype.val (mem_center_iff.mp x.property.1 (⟨t,ht⟩ : (T : Subgroup G)))
  have hxL := pair_sylow_fixed_centralizes_local d h hU hV hne g hout
    (show ((x : (T : Subgroup G)) : G) ∈
      ((F.UH ⊓ centralizer (F.QH : Set G)) ⊓ conjugate F.UH (g : G)) ⊓ centralizer (T : Set G) from
      ⟨⟨hWU hxW,hopp ⟨hxW,hxT⟩⟩,hxT⟩)
  have hL₁L : F.L₁ ≤ L := (map_subtype_le _).trans inf_le_left
  have hx1 : ((x : (T : Subgroup G)) : G) = 1 := by
    have hm : ((x : (T : Subgroup G)) : G) ∈ W ⊓ centralizer (F.L₁ : Set G) :=
      ⟨hxW,centralizer_le (hL₁L.trans le_sup_left) hxL⟩
    rwa [hfixed,mem_bot] at hm
  exact hx (Subtype.ext (Subtype.ext hx1))

/-- The last source13.7.16 contradiction on W=[U₀,K]. The two natural-module
fixed-space calculations remain explicit; component normality is the earlier13.7.15(3). -/
theorem source_fixed_layer_component_commutator_eq_bot
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,H.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    (K : Subgroup G) (hKH : K ≤ H) (hKn : H ≤ normalizer (K : Set G))
    (hfixed : ⁅PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H),K⁆ ⊓
      centralizer ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ : Set G) = ⊥)
    (hopp : ⁅PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H),K⁆ ⊓
      centralizer (T : Set G) ≤ conjugate (Section08.Source.UH H V₃) (g : G)) :
    ⁅PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H),K⁆ = ⊥ := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let U₀ := PlusAction.fixedLayer F
  have hHU₀ : H ≤ normalizer (U₀ : Set G) := PlusAction.fixedLayer_normalized (D := F)
  have hWU : ⁅U₀,K⁆ ≤ U₀ := le_normalizer_iff_commutator_le_left.mp (hKH.trans hHU₀)
  have hTW : (T : Subgroup G) ≤ normalizer ((⁅U₀,K⁆ : Subgroup G) : Set G) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hHU₀ (h.T_le_H ht)),
      mem_normalizer_iff_map_conj_eq.mp (hKn (h.T_le_H ht))]
  exact pair_normal_fixed_layer_eq_bot d h hU hV hne g hout ⁅U₀,K⁆ hWU hTW hfixed hopp

end CFSG.Quasithin.Chapter13.Section07
