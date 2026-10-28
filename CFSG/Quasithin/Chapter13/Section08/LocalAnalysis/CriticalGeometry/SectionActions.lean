module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.SectionActions.Generated
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.SectionActions.Transport
/-!
# Quotient-action branches at the critical pair

The source equality [F̃,Uγ]=[F̃,Vγ] is interpreted in the literal UH/V₁.
Lifting it bounds [F,Vγ] by [F,Uγ]V₁. Endpoint generation proves that this
commutator is noncentral modulo Uγ, yielding the common center V₁Uγ/Uγ
and the nontrivial group of transvections on Vγ/Uγ (13.8.9(2)).

For 13.8.11(1), equality of star images gives that quotient equality, so
13.8.9 supplies a nonidentity transvection. The genuine endpoint conjugator
transports it to the actual H-action on VH/UH, contradicting its exclusion.
RankBounds supplies the line-containment branch and the final rank arithmetic.
The imported Transport module also proves the independent implication for
13.8.18(4), excluding the axis action from absence of transvections in H*.

The earlier source inputs remain explicit:
* the flag containments, elementary abelianness and |V₁|=2 from §§13.2–13.7;
* Vγ≤H, UH≤Gγ, H-normalization of V₁, and [UH,O₂(H)]≤V₁ from F.9;
* the terminal-edge commutator bound from 13.8.4(5);
* [VH,H]≰UH from 13.7.7.
The generation and nontrivial star-image hypotheses are those of 13.8.9/11.
Transport's 13.8.18 implication additionally uses the strict actual D_H
from 13.8.8. The parent source assembly must discharge these earlier inputs;
no quotient-action transport or desired chapter conclusion is assumed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemmas
13.8.9(2), 13.8.11(1), 13.8.18(4), printed pp.949–950 and 953.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.SectionActions.CriticalPair
variable {G : Type*} [Group G] [Finite G] {L T H V : Subgroup G} (c : CriticalPair L T H V)

/-- 13.8.9(2): the source equality is in the literal UH/V₁. -/
theorem center_of_quotient_equality (V₃ V₁ F : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 c.Vgamma]
    (hV₃V : V₃ ≤ V) (hVH : V ≤ H) (hFU : F ≤ Source.UH H V₃)
    (hUJ : Source.UH H V₃ ≤ vertexGroup L T H c.gamma) (hZ : V₁ ≤ Source.UH H V₃)
    (hVF : c.Vgamma ≤ normalizer (F : Set G)) (hline : Nat.card V₁ = 2)
    (hgen : vertexGroup L T H c.gamma =
      conjugateSpanBy F (vertexGroup L T H c.gamma) ⊔ edgeGroup L T H c.gamma c.previous)
    (hedge : ⁅edgeGroup L T H c.gamma c.previous,
      V.map (MulAut.conj (c.gb : G)).toMonoidHom⁆ ≤ c.Ugamma V₃)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (heq : quotientCommutator F (c.Ugamma V₃) (Source.UH H V₃) V₁ =
      quotientCommutator F c.Vgamma (Source.UH H V₃) V₁) :
    HasTransvectionCenter F c.Vgamma (c.Ugamma V₃) V₁
      ((hFU.trans hUJ).trans (c.normalizes_Ugamma V))
      ((hFU.trans hUJ).trans (c.normalizes_Ugamma V₃)) := by
  have hUV : c.Ugamma V₃ ≤ c.Vgamma := map_mono (conjugateSpanBy_mono hV₃V le_rfl)
  have hb := bound_of_quotientCommutator_eq F c.Vgamma (c.Ugamma V₃)
    (Source.UH H V₃) V₁ hFU hZ hVF (hUV.trans hVF) heq.symm
  have hVJ : c.Vgamma ≤ vertexGroup L T H c.gamma := by
    rw [c.vertexGroup_gamma]
    exact map_mono (conjugateSpanBy_le_self hVH)
  exact center_of_bound (vertexGroup L T H c.gamma) F c.Vgamma (c.Ugamma V₃) V₁
    (hFU.trans hUJ) hVJ (hZ.trans hUJ) hUV (c.normalizes_Ugamma V)
    (c.normalizes_Ugamma V₃) hline hb
    (c.noncentral_of_generation V₃ F hVH (hFU.trans hUJ) hgen hedge hnoncentral)

omit [Finite G] in
/-- Equality of the actual star images supplies precisely the source equality
of commutators on UH/V₁, using the earlier F.9.2 core bound. -/
theorem quotient_equality_of_equal_star (V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hV₃V : V₃ ≤ V) (hVH : V ≤ H) (hVγH : c.Vgamma ≤ H)
    (hZ : V₁ ≤ Source.UH H V₃) (hz : H ≤ normalizer (V₁ : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁)
    (heq : Source.starImage H (c.Ugamma V₃) = Source.starImage H c.Vgamma) :
    quotientCommutator (Source.UH H V₃) (c.Ugamma V₃) (Source.UH H V₃) V₁ =
      quotientCommutator (Source.UH H V₃) c.Vgamma (Source.UH H V₃) V₁ := by
  have hUV : c.Ugamma V₃ ≤ c.Vgamma := map_mono (conjugateSpanBy_mono hV₃V le_rfl)
  have hUH : Source.UH H V₃ ≤ H := conjugateSpanBy_le_self (hV₃V.trans hVH)
  have hVF := hVγH.trans (le_normalizer_conjugateSpanBy V₃ H)
  exact quotientCommutator_eq_of_bound (Source.UH H V₃) (c.Ugamma V₃) c.Vgamma
    (Source.UH H V₃) V₁ hUV le_rfl hZ hVF
    (commutator_bound_of_equal_starImage H (Source.UH H V₃) (c.Ugamma V₃) c.Vgamma V₁
      hUH hVγH (hZ.trans hUH) hz hUV hVF hQ heq)

/-- The remaining branch of 13.8.11(1), with actual endpoint transport. -/
theorem strict_star_of_no_v_transvection (V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    [IsElementaryAbelian 2 c.Vgamma]
    (hV₃V : V₃ ≤ V) (hVH : V ≤ H) (hVγH : c.Vgamma ≤ H)
    (hUJ : Source.UH H V₃ ≤ vertexGroup L T H c.gamma)
    (hZ : V₁ ≤ Source.UH H V₃) (hz : H ≤ normalizer (V₁ : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁) (hline : Nat.card V₁ = 2)
    (hgen : vertexGroup L T H c.gamma =
      conjugateSpanBy (Source.UH H V₃) (vertexGroup L T H c.gamma) ⊔
        edgeGroup L T H c.gamma c.previous)
    (hedge : ⁅edgeGroup L T H c.gamma c.previous,
      V.map (MulAut.conj (c.gb : G)).toMonoidHom⁆ ≤ c.Ugamma V₃)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hstar : Source.starImage H (c.Ugamma V₃) ≠ ⊥)
    (hno : ∀ h : H, vAction H V V₃ h ≠ 1 → binaryLinear (vAction H V V₃ h) ∉
      LinearEquiv.transvections (ZMod 2) (Additive (Source.Vsection H V V₃))) :
    Source.starImage H (c.Ugamma V₃) < Source.starImage H c.Vgamma ∧
      1 < rank (Source.starImage H c.Vgamma) := by
  have hUV : c.Ugamma V₃ ≤ c.Vgamma := map_mono (conjugateSpanBy_mono hV₃V le_rfl)
  have hle : Source.starImage H (c.Ugamma V₃) ≤ Source.starImage H c.Vgamma :=
    map_mono (subgroupOf_mono H hUV)
  have hlt : Source.starImage H (c.Ugamma V₃) < Source.starImage H c.Vgamma := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hquot := quotient_equality_of_equal_star c V₃ V₁ hV₃V hVH hVγH hZ hz hQ heq
    have hc := center_of_quotient_equality c V₃ V₁ (Source.UH H V₃) hV₃V hVH le_rfl
      hUJ hZ (hVγH.trans (le_normalizer_conjugateSpanBy V₃ H)) hline hgen hedge hnoncentral hquot
    obtain ⟨p, hp, ht⟩ := exists_nonidentity_of_center (Source.UH H V₃) c.Vgamma
      (c.Ugamma V₃) V₁ _ _ hc
    obtain ⟨h, hh, ht'⟩ := v_transport_nonidentity c V₃ (Source.UH H V₃) hUJ p hp ht
    exact hno h hh ht'
  exact ⟨hlt, rank_gt_one_of_nontrivial_lt _ _ hstar
    (starImage_isElementaryAbelian H c.Vgamma hVγH) hlt⟩

/-- Both alternatives of 13.8.11(1); the first reuses RankBounds. -/
theorem strict_star_of_line_or_no_v_transvection (V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    [IsElementaryAbelian 2 c.Vgamma]
    (hV₃V : V₃ ≤ V) (hVH : V ≤ H) (hVγH : c.Vgamma ≤ H)
    (hUJ : Source.UH H V₃ ≤ vertexGroup L T H c.gamma)
    (hZ : V₁ ≤ Source.UH H V₃) (hz : H ≤ normalizer (V₁ : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁) (hline : Nat.card V₁ = 2)
    (hgen : vertexGroup L T H c.gamma =
      conjugateSpanBy (Source.UH H V₃) (vertexGroup L T H c.gamma) ⊔
        edgeGroup L T H c.gamma c.previous)
    (hedge : ⁅edgeGroup L T H c.gamma c.previous,
      V.map (MulAut.conj (c.gb : G)).toMonoidHom⁆ ≤ c.Ugamma V₃)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hstar : Source.starImage H (c.Ugamma V₃) ≠ ⊥)
    (hor : V₁ ≤ c.Ugamma V₃ ∨
      ∀ h : H, vAction H V V₃ h ≠ 1 → binaryLinear (vAction H V V₃ h) ∉
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Vsection H V V₃))) :
    Source.starImage H (c.Ugamma V₃) < Source.starImage H c.Vgamma ∧
      1 < rank (Source.starImage H c.Vgamma) := by
  rcases hor with hZU | hno
  · have hUH : Source.UH H V₃ ≤ H := conjugateSpanBy_le_self (hV₃V.trans hVH)
    exact starImage_lt_of_noncentral_and_line H (Source.UH H V₃) (c.Ugamma V₃) c.Vgamma V₁
      hUH hVγH (hZ.trans hUH) hz (map_mono (conjugateSpanBy_mono hV₃V le_rfl))
      (hVγH.trans (le_normalizer_conjugateSpanBy V₃ H)) (hUJ.trans (c.normalizes_Ugamma V₃))
      hQ (c.noncentral_of_generation V₃ (Source.UH H V₃) hVH hUJ hgen hedge hnoncentral) hstar hZU
  · exact strict_star_of_no_v_transvection c V₃ V₁ hV₃V hVH hVγH hUJ hZ hz hQ hline
      hgen hedge hnoncentral hstar hno

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.SectionActions.CriticalPair

end
