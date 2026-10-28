module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeRanks
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeInvolutions
public import Theory.GroupTheory.PGroup.NormalSupplementKernel
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPairCentralizers

/-!
# Genuine involution lifts in the original M24-code Sylow subgroup

The literal LT action covers the full original automizer with a two-group
kernel. The original rank-six elementary offender maps to the native sextet
core, meeting both M24 involution classes. Fusion therefore supplies genuine
involutive lifts, and the full two-group kernel places each lift in the same
original Sylow subgroup whenever its image lies there.

Source: Aschbacher--Smith 8.2.8(6), printed p.719, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal action of the original LT on the source orbit. -/
def mathieuJoinAutomizer : (L ⊔ (T : Subgroup G) : Subgroup G) →* Automizer D.sourceOrbit :=
  D.sourceOrbit.normalizerMonoidHom.rangeRestrict.comp
    (inclusion (sup_le D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes))

theorem sourceOrbit_m24_join_cover
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (a : Automizer D.sourceOrbit ≃* M24) :
    Function.Surjective (a.toMonoidHom.comp D.mathieuJoinAutomizer) ∧
      IsPGroup 2 (a.toMonoidHom.comp D.mathieuJoinAutomizer).ker := by
  let J := L ⊔ (T : Subgroup G)
  let LJ := L.subgroupOf J
  let TJ := (T : Subgroup G).subgroupOf J
  let e : LJ ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  have he : D.mathieuJoinAutomizer.comp LJ.subtype =
      D.mathieuComponentAutomizer.comp e.toMonoidHom := rfl
  have hsur := D.sourceOrbit_largeMathieu_component_surjective h hs (.inr hq)
  have hsurJ : Function.Surjective D.mathieuJoinAutomizer := by
    intro b
    obtain ⟨l,hl⟩ := hsur b
    exact ⟨inclusion (show L ≤ J from le_sup_left) l,hl⟩
  refine ⟨a.surjective.comp hsurJ,?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ a.injective]
  let : LJ.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hgen : LJ ⊔ TJ = ⊤ := by
    rw [←subgroupOf_sup (show L ≤ J from le_sup_left) (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hk : IsPGroup 2 (D.mathieuJoinAutomizer.comp LJ.subtype).ker := by
    rw [he,←MonoidHom.comap_ker,D.sourceOrbit_largeMathieu_component_kernel h (.inr hq)]
    exact (pCore_isPGroup (p := 2) (G := L)).comap_of_injective e.toMonoidHom e.injective
  exact MonoidHom.kernel_isPGroup_of_normal_supplement D.mathieuJoinAutomizer LJ TJ
    T.2.comap_subtype hgen hk

theorem sourceOrbit_m24_code_sylow_involution_lifts_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    let J := L ⊔ (T : Subgroup G)
    let f := a.toMonoidHom.comp D.mathieuJoinAutomizer
    ∀ x : M24, orderOf x = 2 → x ∈ ((T : Subgroup G).subgroupOf J).map f →
      ∃ t : T, f ⟨t,mem_sup_right t.property⟩ = x ∧ orderOf t = 2 := by
  let J := L ⊔ (T : Subgroup G)
  let f := a.toMonoidHom.comp D.mathieuJoinAutomizer
  obtain ⟨hf,hk⟩ := D.sourceOrbit_m24_join_cover h.toHypothesis1221
    (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hq a
  obtain ⟨I,i,S,s,hw,_hOff,_hfix,_hker,_hIC,_hr,_hu,_hcor,_hUT,_hTU,c,hc⟩ :=
    D.sourceOrbit_m24_code_rank_six_pair_of_many h hmany hV hq hnon a E hE hH
  let A := offenderNormalizer D.sourceOrbit i.val⁻¹
  have hAT : A ≤ T := (selected_offender_of_parameter_bound s
    D.sourceOrbit_weakClosure_setup (by rw [hw]; rfl)).2.2.2.1
  let : IsElementaryAbelian 2 A := by
    let : IsElementaryAbelian 2 (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom) :=
      IsElementaryAbelian.map _
    exact offender_elementary_of_le (show A ≤ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom from inf_le_left)
  let AJ := A.subgroupOf J
  let : IsElementaryAbelian 2 AJ := IsElementaryAbelian.subgroupOf (hAT.trans le_sup_right)
  have hmap : AJ.map f = (inducedAutomizer D.sourceOrbit A).map a.toMonoidHom := by
    ext b
    constructor
    · rintro ⟨g,hg,rfl⟩
      refine ⟨D.mathieuJoinAutomizer g,?_,rfl⟩
      exact ⟨⟨g,(show A ≤ normalizer (D.sourceOrbit : Set G) from inf_le_right) hg⟩,hg,rfl⟩
    · rintro ⟨b,hb,rfl⟩
      obtain ⟨g,hg,rfl⟩ := mem_map.mp hb
      exact ⟨⟨g,mem_sup_right (hAT hg)⟩,hg,rfl⟩
  have hmark : (AJ.map f).map (MulAut.conj c).toMonoidHom =
      M24LocalGeometry.SextetCore.core := by
    rw [hmap]
    exact hc
  change ∀ x : M24, orderOf x = 2 → x ∈ ((T : Subgroup G).subgroupOf J).map f →
    ∃ t : T, f ⟨t,mem_sup_right t.property⟩ = x ∧ orderOf t = 2
  intro x hx hxT
  obtain ⟨t,ht,ht2⟩ := NormalizedShadowRows.CodeInvolutions.involution_lift_in_sylow
    f hf hk AJ c hmark (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)) x hx hxT
  refine ⟨⟨t.val,t.property⟩,ht,?_⟩
  have he : orderOf (⟨t.val,t.property⟩ : T) = orderOf t := by
    rw [←Subgroup.orderOf_coe,←Subgroup.orderOf_coe,←Subgroup.orderOf_coe]
  exact he.trans ht2

/-- The exact original source inputs already produce the auxiliary HStar
needed for the elementary sextet. No choice of an additional local overgroup
is an assumption of this involution-lifting conclusion. -/
theorem sourceOrbit_m24_code_sylow_involution_lifts
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v)) :
    let J := L ⊔ (T : Subgroup G)
    let f := a.toMonoidHom.comp D.mathieuJoinAutomizer
    ∀ x : M24, orderOf x = 2 → x ∈ ((T : Subgroup G).subgroupOf J).map f →
      ∃ t : T, f ⟨t,mem_sup_right t.property⟩ = x ∧ orderOf t = 2 := by
  let F := D.fundamentalSetup h.toHypothesis1221
  have h127 := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hu := F.lemma_3_2_3_uniqueness h127
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (Chapter3.hasMaximalOutside_of_many T hmany F.maximalLocal hu.1
      ((show (T : Subgroup G) ≤ Chapter3.Section02.localJoin T L from le_sup_right).trans hu.2.1))
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) := by
    simpa only [Chapter3.Section02.FundamentalSetup.maximalLocal,D.localOrbit_eq] using hH
  exact D.sourceOrbit_m24_code_sylow_involution_lifts_of_many h hmany hV hq hnon a E hE hH'

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
