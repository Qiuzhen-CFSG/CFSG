module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldComponent
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldComponentNormal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldComponentControl
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.SourceOvergroups

/-!
# Relative normality of the field residual on the Chapter 12 layer

The actual field residual is a local C-component. Source 1.2.4, applied
inside N_G(U) with its two-core quotient supplied by the Chapter E
hypothesis, places it in a normal C-component. Solvable-overgroup control
and Frattini identify the containing component with the residual itself.
Thus O²(N_L(U)) is normal in N_G(U), discharging the remaining premise of
the natural displacement action on a conjugate line.

Source: Aschbacher–Smith, 6.1.14(5), printed p.671, using 1.2.4 and A.3.3.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G} {n : ℕ}

/-- Source 1.2.4 applied to the actual field residual in N_G(U). -/
theorem source_field_residual_normal_component
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n) (hUne : U ≠ ⊥) (hn : 2 < n)
    (P : Sylow 2 G)
    (hg : FieldFixedSpaceGeometry L (normalizer (L : Set G)) (commutatorLayer T L) U n P) :
    ∃ K : Subgroup (normalizer (U : Set G)), K.IsCComponent ∧
      (fieldLocalResidual L U).subgroupOf (normalizer (U : Set G)) ≤ K ∧ K.Normal := by
  let : IsElementaryAbelian 2 (commutatorLayer T L) := h611.layer_elementary
  let H := normalizer (U : Set G)
  let S := (P : Subgroup G) ⊓ H
  let R := fieldLocalResidual L U
  have hUB : U ≤ commutatorLayer T L := by
    obtain ⟨_, _, _, he, _⟩ := hfield
    exact he.le.trans inf_le_left
  have hBH : commutatorLayer T L ≤ H :=
    ((commutatorLayer T L).le_centralizer.trans (centralizer_le hUB)).trans
      (Subgroup.centralizer_le_normalizer _)
  obtain ⟨hR, hSR⟩ := field_residual_mem_local hnatural hfield hUne hn
    (le_inf hg.module_le hBH) (inf_le_left.trans hg.normalizes_L)
    (inf_le_left.trans hg.normalizes_module) inf_le_right hg.normalizer_sylow
  have hRH : R ≤ H := (map_subtype_le _).trans inf_le_right
  obtain ⟨S₀, hS₀⟩ := hg.normalizer_sylow
  change (S₀ : Subgroup H).map H.subtype = S at hS₀
  have hSub : S.subgroupOf H = (S₀ : Subgroup H) := by
    rw [← hS₀]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hloc : R.subgroupOf H ∈ Chapter1.L H S₀ := by
    rw [← hSub]
    exact (Chapter1.mem_LIn_iff_subgroupOf inf_le_right hRH).mp ⟨hRH, hR⟩
  have hSn : (S₀ : Subgroup H) ≤ normalizer (R.subgroupOf H : Set H) := by
    intro s hs
    apply le_normalizer_comap H.subtype
    exact hSR (show (s : G) ∈ S from hS₀ ▸ mem_map_of_mem H.subtype hs)
  have hH : H ∈ Chapter1.H G := by
    have hu := le_pCoreIn_of_normalizes
      ((IsElementaryAbelian.isPGroup 2 (commutatorLayer T L)).to_le hUB)
      U.le_normalizer (show H ≤ normalizer (U : Set G) from le_rfl)
    intro hz
    exact hUne (bot_unique (hu.trans hz.le))
  have hE := source_natural_layer_hypothesisE61 D h h611 hnatural
  obtain ⟨K, hK, _⟩ := Chapter1.Section02.lemma_1_2_4_containment_normality_source
    (ChapterE.Section06.source_local_twoCore_quotient_sqtk hE hH) S₀ hloc hSn
  exact ⟨K, hK⟩
end CFSG.Quasithin.Chapter12.Section02.RankOneModule

namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G} {n : ℕ}

/-- The local-component identification proves actual relative normality
of O²(N_L(U)) in N_G(U). -/
theorem source_field_residual_normal
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n) (hUne : U ≠ ⊥) (hn : 2 < n) :
    ((fieldLocalResidual L U).subgroupOf (normalizer (U : Set G))).Normal := by
  let : IsElementaryAbelian 2 (commutatorLayer T L) := h611.layer_elementary
  obtain ⟨P, hg⟩ := source_field_fixedSpace_geometry D h h611 hnatural hfield hUne hn
  obtain ⟨K, hK, hDK, hKN⟩ :=
    source_field_residual_normal_component D h h611 hnatural hfield hUne hn P hg
  let H := normalizer (U : Set G)
  let R := fieldLocalResidual L U
  let R₀ := (P : Subgroup G) ⊓ centralizer (U : Set G)
  let C := (centralizer (U : Set G)).subgroupOf H
  let A := R.subgroupOf H
  let M := (normalizer (L : Set G)).subgroupOf H
  have hRH : R ≤ H := (map_subtype_le _).trans inf_le_right
  have hR₀H : R₀ ≤ H := inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hCH : centralizer (U : Set G) ≤ H := Subgroup.centralizer_le_normalizer _
  have hUB : U ≤ commutatorLayer T L := by
    obtain ⟨_, _, _, he, _⟩ := hfield
    exact he.le.trans inf_le_left
  have hBH : commutatorLayer T L ≤ H :=
    ((commutatorLayer T L).le_centralizer.trans (centralizer_le hUB)).trans hCH
  obtain ⟨hloc, _⟩ := field_residual_mem_local hnatural hfield hUne hn
    (le_inf hg.module_le hBH) (inf_le_left.trans hg.normalizes_L)
    (inf_le_left.trans hg.normalizes_module) inf_le_right hg.normalizer_sylow
  have hRp : Group.IsPerfect R := Chapter1.mem_L_isPerfect hloc
  have hAp : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hRH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hRH).symm.surjective
  let := hKN
  apply field_component_normal_of_solvable_control C K A M (R₀.subgroupOf H)
    hK hDK hAp
  · intro hAC
    have hRC : R ≤ centralizer (U : Set G) := fun r hr => hAC (show (⟨r, hRH hr⟩ : H) ∈ A from hr)
    obtain ⟨m, _, _, hnat⟩ := field_fixedSpace_natural hn hnatural hfield hUne
    obtain ⟨F, _, _, _, _, hmodel⟩ := hnat
    have he := hmodel.centralizer_eq_core (Representation.specialLinearNatural_injective 2)
    have hp : IsPGroup 2 R := (isPGroup_pCoreIn 2 R).to_le
      ((le_inf le_rfl hRC).trans he.le)
    let := hp.isNilpotent
    exact Chapter1.mem_L_not_isSolvable hloc inferInstance
  · intro k hk
    apply le_normalizer_comap H.subtype
    have hMN : normalizer (L : Set G) ⊓ H ≤
        normalizer (L ⊓ normalizer (U : Set G) : Set G) :=
      (le_inf inf_le_left (inf_le_right.trans H.le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
    have hMR := hMN.trans (normalizer_le_normalizer_characteristic_image
      (L ⊓ normalizer (U : Set G)) (pResidual 2 (L ⊓ normalizer (U : Set G) : Subgroup G)))
    exact hMR ⟨hk.2, k.property⟩
  · apply (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mp
    change Chapter1.IsSylowIn 2 ((R₀.subgroupOf H).map H.subtype)
      (((centralizer (U : Set G)).subgroupOf H).map H.subtype)
    rw [map_subgroupOf_eq_of_le hR₀H, map_subgroupOf_eq_of_le hCH]
    exact hg.centralizer_sylow
  · intro k hk
    have hh := (R₀.subgroupOf H).le_normalizer_map H.subtype (mem_map_of_mem H.subtype hk)
    rw [map_subgroupOf_eq_of_le hR₀H] at hh
    exact hg.thompson_control (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ R₀ hh)
  · intro X hXsol hXC hRX
    let := hXsol
    let X₀ := X.map H.subtype
    let : Group.IsSolvable X₀ := Group.isSolvable_of_surjective
      (f := (X.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom)
      (X.equivMapOfInjective H.subtype H.subtype_injective).surjective
    have hXC₀ : X₀ ≤ centralizer (U : Set G) := map_le_iff_le_comap.mpr hXC
    have hRX₀ : R₀ ≤ X₀ := by
      have hh := map_mono (f := H.subtype) hRX
      rwa [map_subgroupOf_eq_of_le hR₀H] at hh
    exact map_le_iff_le_comap.mp
      (source_field_solvable_overgroup_le D h h611 hnatural hn P hg X₀ hXC₀ hRX₀)
end CFSG.Quasithin.Chapter12.Section02.RankOneModule
