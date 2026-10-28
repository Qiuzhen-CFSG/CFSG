module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeNear.Native
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows.M22CodeParameters
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneThompson
public import CFSG.Quasithin.Chapter7.Section01To05.FixedSpaceSpan

/-!
# Near-offender displacement on the full M22 code

A near-offender of displacement below six contains an inner involution.
The two native bounds force its rank successively to at most three and two,
contradicting that involution's four-dimensional displacement. Transporting
this result through the full automizer marking makes the first higher
Thompson subgroup centralize the original module whenever the local group
fixes a subspace of rank greater than four. This is the local-action premise
of E.6.27 used in the original M22-code escaping-space argument.
Source: Aschbacher--Smith H.16.5,E.6.27,7.5.6(1), printed pp.404,257,702,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender MathieuCode
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows
open ChapterE ChapterK.Mathieu.OctadGeometry

/-- Every code near-offender has displacement at least six. -/
theorem m22_code_nearOffender_displacement (A : Subgroup m22PairStabilizer)
    (hA : IsElementaryTwo A) (hnear : fixedCodim m22OuterCodeRepresentation A ≤ rank A + 1) :
    6 ≤ fixedCodim m22OuterCodeRepresentation A := by
  let := hA.2
  have hmin := (show 3 ≤ moduleM m22OuterCodeRepresentation from by
    have := ChapterK.Mathieu.m22_code_moduleM_gt_two; omega).trans
      (moduleM_le_fixedCodim m22OuterCodeRepresentation hA)
  by_contra hsmall
  have hsmall : fixedCodim m22OuterCodeRepresentation A < 6 := by omega
  have hr : 1 < rank A := by omega
  obtain ⟨x,hx,hx2,hxi⟩ := m22_exists_inner_involution A hA hr
  have hxi' : x ∈ m22ToPairStabilizer.range :=
    (m22ToPairStabilizer_mem_range_iff_fixed_zero x).mpr hxi
  have hb := NormalizedShadowRows.CodeNear.card_le_eight_of_inner_involution A hsmall x hx hx2 hxi'
  have hr3 : rank A ≤ 3 := (Nat.log_mono_right hb).trans (by decide : Nat.log 2 8 ≤ 3)
  have hs : fixedCodim m22OuterCodeRepresentation A < 5 := by omega
  have hb' := NormalizedShadowRows.CodeNear.card_le_four_of_inner_involution A hs x hx hx2 hxi'
  have hr2 : rank A ≤ 2 := (Nat.log_mono_right hb').trans (by decide : Nat.log 2 4 ≤ 2)
  have hd := m22Outer_cocode_involution_displacement_of_fixed_zero x hx2 hxi
  rw [←m22Outer_code_cocode_fixedCodim_zpowers] at hd
  have hl := Submodule.finrank_mono
    (BinaryOffender.fixedSpace_antitone m22OuterCodeRepresentation (zpowers_le.mpr hx))
  have hf := fixedCodim_add_finrank m22OuterCodeRepresentation A
  have hg := fixedCodim_add_finrank m22OuterCodeRepresentation (zpowers x)
  omega

variable {G : Type*} [Group G] [Finite G] (W : Subgroup G) [IsElementaryAbelian 2 W]

/-- The full original local action fixes a large space, so its first higher
Thompson subgroup centralizes the whole code module. -/
theorem code_local_thompson_bound (A U : Subgroup G)
    (hWA : W ≤ A) (hAN : A ≤ normalizer (W : Set G))
    (hUW : U ≤ W) (hAU : A ≤ centralizer (U : Set G))
    (a : Automizer W →* m22PairStabilizer) (hinj : Function.Injective a)
    (E : Additive W ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ b v, E (automizerRepresentation W b v) = m22OuterCodeRepresentation (a b) (E v))
    (hr : 4 < rank U) : ChapterB.thompsonJ A 1 ≤ centralizer (W : Set G) := by
  apply sSup_le
  intro B hB
  by_contra hn
  let := hB.2.1
  have hBN := hB.1.trans hAN
  let I := inducedAutomizer W B
  have hI : IsElementaryTwo I :=
    ⟨fun hb => hn ((inducedAutomizer_eq_bot_iff hBN).mp hb),inducedAutomizer_elementary W B hBN⟩
  have hIm : IsElementaryTwo (I.map a) := by
    let := hI.2
    exact ⟨fun hb => hI.1 ((I.map_eq_bot_iff_of_injective hinj).mp hb),IsElementaryAbelian.map a⟩
  have hnear := thompson_family_fixedCodim_le W A hWA hAN B hB
  rw [fixedCodim_map_equivariant (automizerRepresentation W) m22OuterCodeRepresentation
    a E hE,←rank_map_injective a hinj] at hnear
  have hd := m22_code_nearOffender_displacement (I.map a) hIm hnear
  rw [←fixedCodim_map_equivariant (automizerRepresentation W) m22OuterCodeRepresentation
    a E hE] at hd
  let X := (Chapter7.moduleSubgroup W).symm (U.subgroupOf W)
  have hX : X ≤ fixedSpace (automizerRepresentation W) I := by
    intro v hv
    apply (mem_fixedSpace_inducedAutomizer W B hBN v).mpr
    exact le_centralizer_iff.mp (hB.1.trans hAU) hv
  have hrX : Module.finrank (ZMod 2) X = rank U := by
    rw [←Chapter7.ambientSubmodule_log_card W,Chapter7.ambientSubmodule,
      (Chapter7.moduleSubgroup W).apply_symm_apply,map_subgroupOf_eq_of_le hUW]
    rfl
  have hdim := E.finrank_eq.trans finrank_m22Code
  have he := fixedCodim_add_finrank (automizerRepresentation W) I
  have hm := Submodule.finrank_mono hX
  omega
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows
