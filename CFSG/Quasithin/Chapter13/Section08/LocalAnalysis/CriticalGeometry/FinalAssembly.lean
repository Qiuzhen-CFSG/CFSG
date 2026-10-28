module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Elementary
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.SectionActions
public import Theory.ElementaryAbelian.BinaryQuotientRank
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.PreliminaryGeometry

/-!
# Completing the critical geometry of §13.8

The selected binary rank comparison is converted to the literal subgroup
indices. Corrected 13.8.10 then gives both one-dimensional quotients, the
actual common-axis action, and a constructed reversed critical pair.
The full-denominator branches construct nonidentity quotient transvections;
their absence therefore forces both denominators to be strict. Endpoint
transport excludes a common-axis transvection, and the proved component
commutator and generation arguments yield 13.8.18(4).

`generated_section_conclusions` assembles both parts of 13.8.9 on Vγ/Uγ.
`generated_rank_conclusions` assembles both rank deductions of 13.8.11.
Both derive the terminal-edge commutator bound from the index-two flag.
`alternatives_from_earlier_inputs` discharges the quadratic-action premise
of the complete corrected 13.8.8 alternative. Finally,
`exists_selected_component_rank` constructs one pair carrying the complete
strict alternative, every-F generation, and the last rank bound together;
its rank comparison is proved by selection, not assumed.

Earlier inputs remain explicit, as required by the parent local analysis:
* the flag, noncentrality and centralizer bounds in 13.5 and 13.7;
* F.9.11/13/15, the proper edge and its two-core containment, and the
  factor-two fixed-codimension estimate of F.9.16(2);
* the genuine faithful central-section realization and complete 13.8.5
  model implication (only for the first alternative of 13.8.8);
* H=K(L₁T), relative normality and two-perfectness of the endpoint component,
  and quasisimplicity of its actual image in Gγ/O₂(Gγ).
No symmetry, desired rank bound, full component commutator, or unidentified
module model is an input. The source standing-counterexample assembly and
discharge of these explicitly authorized earlier inputs remain with the parent.

The two source corrections are explicit: 13.8.10 uses D_H<U_H; the
`Reorientation` formulation of 13.8.8 retains the distinct transported
vertex g_b⁻¹γ₁ and the actual actors constructed by the proof, rather than
identifying it with the printed g_b⁻¹γ=γ₁.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.7–11
and 13.8.18, printed pp.948–950 and 953 (PDF pp.965–967 and 970).
-/

@[expose] public section

open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
open AsymmetricPair Reorientation SectionActions
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
variable {G : Type*} [Group G] [Finite G] {L T H V : Subgroup G}

namespace CriticalPair
variable (c : CriticalPair L T H V)

/-- Convert the selected binary rank comparison to the actual subgroup indices. -/
theorem index_comparison_of_selected_rank (V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hγH : c.Ugamma V₃ ≤ H)
    (hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ =
      c.Ugamma V₃ ⊓ Source.QH H)
    (hcomp : denominatorRank V₃ V₁ c ≤ rank (Source.starImage H (c.Ugamma V₃))) :
    (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex (Source.UH H V₃) ≤
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃) := by
  let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  have hc : Nat.card (Source.starImage H (c.Ugamma V₃)) =
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃) := by
    rw [hDγ, inf_relIndex_left, starImage_card H _ hγH]
  change Nat.log 2 _ ≤ Nat.log 2 _ at hcomp
  rw [hc, log_relIndex_eq_quotient_finrank, log_relIndex_eq_quotient_finrank] at hcomp
  rw [relIndex_eq_two_pow_quotient_finrank, relIndex_eq_two_pow_quotient_finrank]
  exact Nat.pow_le_pow_right (by decide) hcomp

/-- Corrected 13.8.10, including a constructed reverse critical pair. -/
theorem rank_one_corrected (V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hV₃ : V₃ ≤ V) (hz : H ≤ normalizer (V₁ : Set G))
    (hgeo : EarlierGeometry c V₃ V₁)
    (hcomp : denominatorRank V₃ V₁ c ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hrank : rank (Source.starImage H (c.Ugamma V₃)) = 1)
    (hproper : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hline : Nat.card V₁ = 2) :
    let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
    Module.finrank (ZMod 2) (Additive (Source.UH H V₃ ⧸
      (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).subgroupOf (Source.UH H V₃))) = 1 ∧
    Module.finrank (ZMod 2) (Additive (c.Ugamma V₃ ⧸
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).subgroupOf (c.Ugamma V₃))) = 1 ∧
    Nonempty (Reversal c) ∧
    (V₁ ≤ c.Ugamma V₃ ∨ HasTransvectionAxis (Source.UH H V₃) (c.Ugamma V₃)
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁)
      (((conjugateSpanBy_mono hV₃ le_rfl).trans hgeo.VH_endpoint).trans
        (c.normalizes_Ugamma V₃))) := by
  let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  have hγH : c.Ugamma V₃ ≤ H := (map_mono (conjugateSpanBy_mono hV₃ le_rfl)).trans hgeo.Vgamma_H
  have he : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)) := by
    refine ⟨?_, starImage_isElementaryAbelian H _ hγH⟩
    intro hbot
    rw [hbot, Representation.BinaryOffender.rank_bot] at hrank
    contradiction
  have hc : Nat.card (Source.starImage H (c.Ugamma V₃)) = 2 := by
    simpa only [hrank, pow_one] using he.card_eq_two_pow_rank
  have hh := corrected_rank_one_of_starImage H (Source.UH H V₃) (c.Ugamma V₃)
    (c.Aone V₁) V₁ hγH hc hgeo.Dgamma_kernel hproper
    (c.index_comparison_of_selected_rank V₃ V₁ hγH hgeo.Dgamma_kernel hcomp) hline
    (((conjugateSpanBy_mono hV₃ le_rfl).trans hgeo.VH_endpoint).trans (c.normalizes_Ugamma V₃))
    (hγH.trans hz)
  have hs : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃ := by
    refine lt_of_le_of_ne (commutatorPreimage_le _ _ _) ?_
    intro heq
    have hi : (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃) = 2 := by
      rw [hgeo.Dgamma_kernel, inf_relIndex_left, ← starImage_card H _ hγH, hc]
    rw [heq, relIndex_self] at hi
    contradiction
  exact ⟨hh.1, hh.2.1, exists_reversal_of_strict c V₃ V₁ hgeo.length hV₃
    hgeo.Vgamma_H hz hgeo.first_kernel hs, hh.2.2⟩

/-- Absence of transvections on the literal central quotient forces both
strict denominators, by constructing the actors in each full-denominator case. -/
theorem strict_denominators_of_no_uStar_transvection (V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hV₃ : V₃ ≤ V) (hz : H ≤ normalizer (V₁ : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁)
    (hgeo : EarlierGeometry c V₃ V₁) (hline : Nat.card V₁ = 2)
    (hcentral : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ V₁)
    (hbad : ¬ ⁅c.Ugamma V₃, V⁆ ≤ c.Aone V₁)
    (hno : ∀ h : Source.Hstar H, uStarAction H V₃ V₁ hz hQ h ≠ 1 →
      binaryLinear (uStarAction H V₃ V₁ hz hQ h) ∉
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁))) :
    Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃ ∧
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃ := by
  let Q : CenterQuotientAction H (Source.UH H V₃) V₁ := {
    normalizes := le_normalizer_conjugateSpanBy V₃ H
    action := uAction H V₃ V₁ hz
    apply_mk := quotientAction_apply H (Source.UH H V₃) V₁ _ hz }
  have hforbid {P : Subgroup G} (ht : TransvectionGroup Q P) : False := by
    obtain ⟨t, _, hn, ht⟩ := ht.nonidentity_actor
    have hh := hno (QuotientGroup.mk' (pCore 2 H) t)
    rw [uStarAction_mk] at hh
    exact hh hn ht
  have hγH : c.Ugamma V₃ ≤ H := (map_mono (conjugateSpanBy_mono hV₃ le_rfl)).trans hgeo.Vgamma_H
  have hUA : Source.UH H V₃ ≤ normalizer (c.Aone V₁ : Set G) :=
    ((conjugateSpanBy_mono hV₃ le_rfl).trans hgeo.VH_endpoint).trans
      (SectionActions.CriticalPair.normalizes_Aone c V₁ hz)
  have hs : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃ := by
    by_contra hh
    have he := eq_of_le_of_not_lt (commutatorPreimage_le _ _ _) hh
    rcases transvection_of_Dgamma_eq c V₃ V₁ Q hV₃ hz hline hγH hgeo.VH_endpoint hUA
      hgeo.lines_disjoint hcentral hbad he with ht | ht
    · exact hforbid ht
    · exact hforbid ht
  refine ⟨?_, hs⟩
  by_contra hh
  have he := eq_of_le_of_not_lt (commutatorPreimage_le _ _ _) hh
  exact hforbid (transvection_of_DH_eq_Dgamma_lt c V₃ V₁ Q hline hγH hUA
    hgeo.lines_disjoint he hs)

/-- 13.8.18(4) for the critical pair selected in 13.8.8. Strictness,
component generation and exclusion of the endpoint axis are all discharged. -/
theorem rank_gt_one_of_component_no_uStar_transvection
    (L₁ K V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    (hH : H = K ⊔ (L₁ ⊔ T)) (he : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hK : ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H c.gamma)).Normal)
    (hres : pResidual 2 ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H c.gamma)) = ⊤)
    (hqs : IsQuasisimple (Source.starImage (vertexGroup L T H c.gamma)
      (K.map (MulAut.conj (c.gb : G)).toMonoidHom)))
    (hU : Source.UH H V₃ ≤ (edgeGroup L T H c.gamma c.previous).pCoreIn 2)
    (hV₃ : V₃ ≤ V) (hVH : V ≤ H) (hV₁H : V₁ ≤ H)
    (hz : H ≤ normalizer (V₁ : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁)
    (hgeo : EarlierGeometry c V₃ V₁) (hline : Nat.card V₁ = 2)
    (hcentral : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ V₁)
    (hbad : ¬ ⁅c.Ugamma V₃, V⁆ ≤ c.Aone V₁)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hedge : ⁅edgeGroup L T H c.gamma c.previous,
      V.map (MulAut.conj (c.gb : G)).toMonoidHom⁆ ≤ c.Ugamma V₃)
    (hQE : c.Qgamma ≤ edgeGroup L T H c.gamma c.previous)
    (hEJ : edgeGroup L T H c.gamma c.previous < vertexGroup L T H c.gamma)
    (hcomp : denominatorRank V₃ V₁ c ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hno : ∀ h : Source.Hstar H, uStarAction H V₃ V₁ hz hQ h ≠ 1 →
      binaryLinear (uStarAction H V₃ V₁ hz hQ h) ∉
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁))) :
    1 < rank (Source.starImage H c.Vgamma) := by
  let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  obtain ⟨hDH, hDγ⟩ := c.strict_denominators_of_no_uStar_transvection V₃ V₁ hV₃ hz hQ
    hgeo hline hcentral hbad hno
  have hUJ := hU.trans ((pCoreIn_le 2 _).trans inf_le_left)
  have haxis := SectionActions.CriticalPair.no_axis_of_no_uStar_transvection c V₃ V₁
    hz hQ hUJ hDH hno
  have hγH := (map_mono (conjugateSpanBy_mono hV₃ le_rfl)).trans hgeo.Vgamma_H
  exact c.rank_gt_one_of_component_generation L₁ K V₃ V₁ hH he hK hres hqs hU hgeo.DH_kernel
    hV₃ hVH hV₁H hz hgeo.Vgamma_H hQ hnoncentral hedge hgeo.Dgamma_kernel hDH hDγ
    hQE hEJ (c.index_comparison_of_selected_rank V₃ V₁ hγH hgeo.Dgamma_kernel hcomp) hline haxis

/-- Both clauses of 13.8.9, with the terminal-edge action deduced from the
index-two flag. The second clause acts on the literal Vγ/Uγ and identifies its
nontrivial center as the actual image of V₁. -/
theorem generated_section_conclusions (V₃ V₁ F : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    (hV₃ : V₃ ≤ V) (hVH : V ≤ H) (hFU : F ≤ Source.UH H V₃)
    (hUJ : Source.UH H V₃ ≤ vertexGroup L T H c.gamma)
    (hZ : V₁ ≤ Source.UH H V₃) (hVF : c.Vgamma ≤ normalizer (F : Set G))
    (hline : Nat.card V₁ = 2)
    (hgen : vertexGroup L T H c.gamma =
      conjugateSpanBy F (vertexGroup L T H c.gamma) ⊔ edgeGroup L T H c.gamma c.previous)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hindex : V₃.relIndex V = 2) (hnorm : (L ⊔ T) ⊓ H ≤ normalizer (V : Set G)) :
    let _ : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
    ¬ ⁅F, c.Vgamma⁆ ≤ c.Ugamma V₃ ∧
      (quotientCommutator F (c.Ugamma V₃) (Source.UH H V₃) V₁ =
        quotientCommutator F c.Vgamma (Source.UH H V₃) V₁ →
      HasTransvectionCenter F c.Vgamma (c.Ugamma V₃) V₁
        ((hFU.trans hUJ).trans (c.normalizes_Ugamma V))
        ((hFU.trans hUJ).trans (c.normalizes_Ugamma V₃))) := by
  let _ : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le (show V ≤ Source.VH H V from le_conjugateSpanBy V H)
  let _ : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
  have hedge := c.edge_commutator_le_of_flag V₃ hV₃ hindex hnoncentral hnorm
  exact ⟨c.noncentral_of_generation V₃ F hVH (hFU.trans hUJ) hgen hedge hnoncentral,
    fun heq => SectionActions.CriticalPair.center_of_quotient_equality c V₃ V₁ F
      hV₃ hVH hFU hUJ hZ hVF hline hgen hedge hnoncentral heq⟩

/-- Both rank deductions of 13.8.11 for the selected pair. Generation is
exactly the printed hypothesis; its proper edge forces D_H<U_H in part (2). -/
theorem generated_rank_conclusions (V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    (hV₃ : V₃ ≤ V) (hVH : V ≤ H) (hZ : V₁ ≤ Source.UH H V₃)
    (hz : H ≤ normalizer (V₁ : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁)
    (hgeo : EarlierGeometry c V₃ V₁) (hline : Nat.card V₁ = 2)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hindex : V₃.relIndex V = 2) (hnorm : (L ⊔ T) ⊓ H ≤ normalizer (V : Set G))
    (hstar : Source.starImage H (c.Ugamma V₃) ≠ ⊥)
    (hgen : vertexGroup L T H c.gamma =
      conjugateSpanBy (Source.UH H V₃) (vertexGroup L T H c.gamma) ⊔
        edgeGroup L T H c.gamma c.previous)
    (hQE : c.Qgamma ≤ edgeGroup L T H c.gamma c.previous)
    (hEJ : edgeGroup L T H c.gamma c.previous < vertexGroup L T H c.gamma)
    (hcomp : denominatorRank V₃ V₁ c ≤ rank (Source.starImage H (c.Ugamma V₃))) :
    let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
    ((V₁ ≤ c.Ugamma V₃ ∨
      ∀ h : H, vAction H V V₃ h ≠ 1 → binaryLinear (vAction H V V₃ h) ∉
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Vsection H V V₃))) →
      Source.starImage H (c.Ugamma V₃) < Source.starImage H c.Vgamma ∧
        1 < rank (Source.starImage H c.Vgamma)) ∧
    (¬ HasTransvectionAxis (Source.UH H V₃) (c.Ugamma V₃)
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁)
      (((conjugateSpanBy_mono hV₃ le_rfl).trans hgeo.VH_endpoint).trans (c.normalizes_Ugamma V₃)) →
      1 < rank (Source.starImage H c.Vgamma)) := by
  let _ : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le (show V ≤ Source.VH H V from le_conjugateSpanBy V H)
  let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
  have hUJ := (conjugateSpanBy_mono hV₃ le_rfl).trans hgeo.VH_endpoint
  have hZH := hZ.trans (conjugateSpanBy_le_self (hV₃.trans hVH))
  have hγH := (map_mono (conjugateSpanBy_mono hV₃ le_rfl)).trans hgeo.Vgamma_H
  have hedge := c.edge_commutator_le_of_flag V₃ hV₃ hindex hnoncentral hnorm
  refine ⟨fun hor => SectionActions.CriticalPair.strict_star_of_line_or_no_v_transvection c
    V₃ V₁ hV₃ hVH hgeo.Vgamma_H hUJ hZ hz hQ hline hgen hedge hnoncentral hstar hor, ?_⟩
  intro hno
  exact c.rank_gt_one_of_generation_no_axis V₃ V₁ hV₃ hVH hZH hz hgeo.Vgamma_H hUJ
    hQ hnoncentral hgen hedge hstar hgeo.Dgamma_kernel hgeo.DH_kernel hQE hEJ
    (c.index_comparison_of_selected_rank V₃ V₁ hγH hgeo.Dgamma_kernel hcomp) hline hno

end CriticalPair

namespace Reorientation
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  {ρ : Representation (ZMod 2) (Source.Hstar H) E}

/-- The complete corrected 13.8.8 alternatives with 13.8.4(6) discharged.
Only the precise earlier geometry, model implication and F.9.16 estimate remain. -/
theorem alternatives_from_earlier_inputs
    (c : CriticalPair L T H V) (L₁ R₁ V₃ Z : Subgroup G) (hL₁ : L₁ ≤ H)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)] [(Z.subgroupOf (Source.UH H V₃)).Normal]
    (Q : CenterQuotientAction H (Source.UH H V₃) Z)
    (s : ConjugationSection H (Source.UH H V₃) Z ρ) (hfaith : Function.Injective ρ)
    (hV₃ : V₃ ≤ V) (hcard : Nat.card Z = 2)
    (hgeo : ∀ d : CriticalPair L T H V, EarlierGeometry d V₃ Z)
    (hbad : ¬ ⁅c.Ugamma V₃, V⁆ ≤ c.Aone Z)
    (hcentral : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ Z)
    (hmodels : (∃ t : H, Q.action t ≠ 1 ∧ binaryLinear (Q.action t) ∈
      LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ Z))) →
      FullModelConclusions L L₁ T hL₁ Q)
    (hF916 : ∀ d : CriticalPair L T H V,
      0 < rank (Source.starImage H (d.Ugamma V₃)) →
      denominatorRank V₃ Z d ≤ rank (Source.starImage H (d.Ugamma V₃)) →
      fixedCodim ρ (Source.starImage H (d.Ugamma V₃)) ≤
        2 * rank (Source.starImage H (d.Ugamma V₃)))
    (hedge : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hcore : ∀ d : CriticalPair L T H V,
      d.Vgamma ≤ (edgeGroup L T H (base L T H true) d.second).pCoreIn 2)
    (hR : (L₁ ⊔ T).pCoreIn 2 ≤ R₁) :
    (TransvectionAlternative c V₃ Z Q ∧ FullModelConclusions L L₁ T hL₁ Q) ∨
      SelectedAlternative (L := L) (T := T) (V := V) L₁ R₁ V₃ Z ρ := by
  exact alternatives_corrected c L₁ R₁ V₃ Z hL₁ Q s hfaith hV₃ hcard hgeo hbad hcentral
    hmodels (fun d => (d.quadratic_star_on_Utilde V₃ Z s hV₃ (hgeo d).VH_endpoint).2)
    hF916 hedge hcore hR

end Reorientation

namespace CriticalPair
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  {ρ : Representation (ZMod 2) (Source.Hstar H) E}

/-- Select the critical pair in 13.8.8(2) and discharge the selected-rank
premise of 13.8.18(4). All component hypotheses refer to the actual endpoint
quotients. The result retains the offender, edge placement, every-F generation
and the rank conclusion on the same selected pair. -/
theorem exists_selected_component_rank
    (c : CriticalPair L T H V) (L₁ R₁ K V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ) (hfaith : Function.Injective ρ)
    (hH : H = K ⊔ (L₁ ⊔ T)) (he : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hK : ∀ d : CriticalPair L T H V,
      ((K.map (MulAut.conj (d.gb : G)).toMonoidHom).subgroupOf
        (vertexGroup L T H d.gamma)).Normal)
    (hres : ∀ d : CriticalPair L T H V,
      pResidual 2 ((K.map (MulAut.conj (d.gb : G)).toMonoidHom).subgroupOf
        (vertexGroup L T H d.gamma)) = ⊤)
    (hqs : ∀ d : CriticalPair L T H V,
      IsQuasisimple (Source.starImage (vertexGroup L T H d.gamma)
        (K.map (MulAut.conj (d.gb : G)).toMonoidHom)))
    (hU : ∀ d : CriticalPair L T H V,
      Source.UH H V₃ ≤ (edgeGroup L T H d.gamma d.previous).pCoreIn 2)
    (hV₃ : V₃ ≤ V) (hVH : V ≤ H)
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁)
    (hgeo : ∀ d : CriticalPair L T H V, EarlierGeometry d V₃ V₁)
    (hline : Nat.card V₁ = 2)
    (hcentral : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ V₁)
    (hbad : ∀ d : CriticalPair L T H V, ¬ ⁅d.Ugamma V₃, V⁆ ≤ d.Aone V₁)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hindex : V₃.relIndex V = 2)
    (hnorm : (L ⊔ T) ⊓ H ≤ normalizer (V : Set G))
    (hQE : ∀ d : CriticalPair L T H V, d.Qgamma ≤ edgeGroup L T H d.gamma d.previous)
    (hEJ : ∀ d : CriticalPair L T H V,
      edgeGroup L T H d.gamma d.previous < vertexGroup L T H d.gamma)
    (hF916 : ∀ d : CriticalPair L T H V,
      0 < rank (Source.starImage H (d.Ugamma V₃)) →
      denominatorRank V₃ V₁ d ≤ rank (Source.starImage H (d.Ugamma V₃)) →
      fixedCodim ρ (Source.starImage H (d.Ugamma V₃)) ≤
        2 * rank (Source.starImage H (d.Ugamma V₃)))
    (hcore : ∀ d : CriticalPair L T H V,
      d.Vgamma ≤ (edgeGroup L T H (base L T H true) d.second).pCoreIn 2)
    (hR : (L₁ ⊔ T).pCoreIn 2 ≤ R₁)
    (hno : ∀ h : Source.Hstar H,
      uStarAction H V₃ V₁ (s.centralizes.trans (centralizer_le_normalizer _)) hQ h ≠ 1 →
      binaryLinear (uStarAction H V₃ V₁ (s.centralizes.trans (centralizer_le_normalizer _)) hQ h) ∉
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁))) :
    ∃ d : CriticalPair L T H V,
      Source.DH (Source.UH H V₃) (d.Ugamma V₃) (d.Aone V₁) < Source.UH H V₃ ∧
      Source.Dgamma (d.Ugamma V₃) (Source.UH H V₃) V₁ < d.Ugamma V₃ ∧
      0 < rank (Source.starImage H (d.Ugamma V₃)) ∧
      denominatorRank V₃ V₁ d ≤ rank (Source.starImage H (d.Ugamma V₃)) ∧
      QuadraticMember ρ (Source.starImage H (d.Ugamma V₃)) ∧
      (∃ h : H, inG0 (L := L) (T := T) h • d.second = base L T H false ∧
        d.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2 ∧
        (L₁ ⊔ T).pCoreIn 2 ≤ R₁) ∧
      (∀ F : Subgroup G, F ≤ Source.UH H V₃ →
        ¬ F ≤ Source.DH (Source.UH H V₃) (d.Ugamma V₃) (d.Aone V₁) →
        vertexGroup L T H d.gamma = conjugateSpanBy F (vertexGroup L T H d.gamma) ⊔
          edgeGroup L T H d.gamma d.previous) ∧
      1 < rank (Source.starImage H d.Vgamma) := by
  let _ : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le (show V ≤ Source.VH H V from le_conjugateSpanBy V H)
  have hz := s.centralizes.trans (centralizer_le_normalizer _)
  obtain ⟨hDH, hDγ⟩ := c.strict_denominators_of_no_uStar_transvection V₃ V₁ hV₃ hz hQ
    (hgeo c) hline hcentral (hbad c) hno
  obtain ⟨d, hd, hdγ, hp, hc, hquad⟩ := exists_quadratic_selection V₃ V₁ c s hfaith
    (hgeo c).length hV₃ (fun d => (hgeo d).Vgamma_H)
    ((conjugateSpanBy_mono hV₃ le_rfl).trans (hgeo c).VH_endpoint) (hgeo c).first_kernel
    hDH hDγ (fun d => (d.quadratic_star_on_Utilde V₃ V₁ s hV₃ (hgeo d).VH_endpoint).2) hF916
  obtain ⟨h, hh, hv, _⟩ := exists_second_to_base d L₁ R₁
    (by have := (hgeo d).length; omega) he (hcore d) hR
  exact ⟨d, hd, hdγ, hp, hc, hquad, ⟨h, hh, hv, hR⟩,
    d.generation_all L₁ K V₃ V₁ hH he (hK d) (hres d) (hqs d) (hU d) (hgeo d).DH_kernel,
    d.rank_gt_one_of_component_no_uStar_transvection L₁ K V₃ V₁ hH he (hK d) (hres d)
      (hqs d) (hU d) hV₃ hVH (s.line_le.trans s.le) hz hQ (hgeo d) hline hcentral (hbad d)
      hnoncentral (d.edge_commutator_le_of_flag V₃ hV₃ hindex hnoncentral hnorm)
      (hQE d) (hEJ d) hc hno⟩

end CriticalPair
end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry

end
