module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Selection
public import CFSG.Quasithin.ChapterB.Section02.QuadraticSubactor
public import Theory.GroupTheory.FixedCentralizerReplacement

/-!
# Uniform fixed centralizers and an actual outside offender

For every A in the literal Delta family, quadratic replacement inside A U_H
has the same nontrivial two-core quotient image by inclusion-minimality.
The sharp chief-action theorem applies to that replacement. The elementary
fixed-centralizer transport then recovers C_U_H(A)=C_U_H(A∩O₂(H)) for the
original A. Conjugacy carries the result from the fixed Sylow subgroup to
all of Delta, and the image-family selection theorem constructs Sigma outside T.

These theorems discharge the fixed-centralizer and nonemptiness premises of
the plane consumer. They do not infer quadraticity of the original actor
from equality of quotient images; that and the marked chief-factor conclusions
remain with the offender-plane owner. The parent qt-e-152-plane-geometry owns
the preceding small-action and wreath inputs in the final source assembly.

Source: Aschbacher--Smith D.1.3(3), 15.1.12(2), and 15.2.9--11,
printed pp.174--175,1090,1110--1111.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section02
open ChosenGeometry Section01 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

set_option backward.isDefEq.respectTransparency false in
/-- A quadratic maximum replacement for a specified original Delta member,
retaining both inclusions that identify its literal two-core quotient image.
This does not assert quadraticity of the original actor. -/
theorem ChosenSmallSource.delta_quadratic_replacement_in_sylow
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    (hA : A ∈ delta H) (hAT : A ≤ (T : Subgroup G)) :
    ∃ D ∈ elementaryAbelianMaxSubgroups (T.subtype hH.1.1.2 : Subgroup H),
      ¬ D ≤ pCore 2 H ∧
      ¬ D ≤ centralizer ((conjugateSpan H V).subgroupOf H : Set H) ∧
      IsQuadratic (normalRepresentation ((conjugateSpan H V).subgroupOf H)) D ∧
      D ≤ A.subgroupOf H ⊔ (conjugateSpan H V).subgroupOf H ∧
      A.subgroupOf H ≤ D ⊔ pCore 2 H := by
  let := h.prepared.elementary
  let d := source_chosenNormalizer_qrcConfiguration h.ambient T h.empty h.maximal
    h.centralizing h.prepared.le_selected h.prepared.nontrivial h.prepared.normalized
    h.prepared.seed_span hH
  have hq := (source_chosen_equality_inputs h.ambient T h.empty h.maximal hH h.centralizing
    h.prepared.le_selected h.prepared.nontrivial h.prepared.normalized h.prepared.seed_span
    h.prepared.le_local h.prepared.quadratic_ratio).1
  have hnf := source_notFF_of_ratio_two d hq
  have hV := h.prepared.inside_core H hH
  let := source_elementary_span_of_notFF d hV hnf
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  let S := T.subtype hH.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le hH.1.1.2
  let A₀ := A.subgroupOf H
  have hA₀ : A₀ ∈ elementaryAbelianMaxSubgroups (S : Subgroup H) := by
    apply (maxFamily_sylow_iff S A₀).mpr
    refine ⟨fun a ha => hAT ha, ?_⟩
    apply (maxFamily_map_injective_iff H.subtype H.subtype_injective ⊤ A₀).mp
    simpa only [A₀,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hA.1.1] using hA.1
  have hA₀n : ¬ A₀ ≤ pCore 2 H := by
    intro hn
    have hh := map_mono (f := H.subtype) hn
    rw [map_subgroupOf_eq_of_le hA.1.1] at hh
    exact hA.2.1 hh
  have hUS : U ≤ S := by
    intro u hu
    have ht := right_core_le_sylow d ((span_le_right_core d hV) hu)
    exact ht
  have hUN : U ≤ pCore 2 H := by
    intro u hu
    obtain ⟨x, hx, he⟩ := span_le_right_core d hV hu
    exact H.subtype_injective he ▸ hx
  have hAn : ¬ A₀ ≤ centralizer (U : Set H) := by
    intro hc
    exact hA₀n ((le_inf hA₀.1 hc).trans
      (source_span_centralizer_sylow_le_core d h.prepared.nontrivial hV hnf S hS))
  obtain ⟨D,hD,hDn,hDq,hDA⟩ := ChapterB.maxElementary_exists_quadratic_subactor U S A₀ hUS hA₀ hAn
  have hDN : ¬ D ≤ pCore 2 H :=
    fun hn => hDn (source_max_actor_in_core_centralizes d hnf S hS D hD hn)
  have hDm : D.map H.subtype ∈ elementaryAbelianMaxSubgroups H := by
    have hh := (maxFamily_sylow_iff S D).mp hD
    have hm := (maxFamily_map_injective_iff H.subtype H.subtype_injective ⊤ D).mpr hh.2
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hm
  have hDmn : ¬ D.map H.subtype ≤ twoCoreIn H := by
    intro hn
    exact hDN ((map_le_map_iff_of_injective H.subtype_injective).mp hn)
  have hAD : A₀ ≤ D ⊔ pCore 2 H := by
    have hh : D.map H.subtype ≤ A ⊔ twoCoreIn H := by
      have hm := map_mono (f := H.subtype) (hDA.trans (sup_le_sup_left hUN A₀))
      change D.map H.subtype ≤ A ⊔ (pCore 2 H).map H.subtype
      simpa only [A₀,Subgroup.map_sup,map_subgroupOf_eq_of_le hA.1.1] using hm
    have hmin := hA.2.2 _ hDm hDmn ((offenderImage_le_iff hDm.1 hA.1.1).mpr hh)
    have hm := (offenderImage_le_iff hA.1.1 hDm.1).mp hmin
    change A ≤ D.map H.subtype ⊔ (pCore 2 H).map H.subtype at hm
    rw [←map_subgroupOf_eq_of_le hA.1.1,←Subgroup.map_sup] at hm
    exact (map_le_map_iff_of_injective H.subtype_injective).mp hm
  exact ⟨D,hD,hDN,hDn,hDq,hDA,hAD⟩

/-- The fixed-centralizer clause of 15.1.12(2) for every inclusion-minimal
quotient image represented inside the fixed Sylow subgroup. -/
theorem ChosenSmallSource.delta_fixed_in_sylow
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hA : A ∈ delta H) (hAT : A ≤ (T : Subgroup G)) :
    conjugateSpan H V ⊓ centralizer (A : Set G) =
      conjugateSpan H V ⊓ centralizer (A ⊓ twoCoreIn H : Subgroup G) := by
  let := h.prepared.elementary
  let d := source_chosenNormalizer_qrcConfiguration h.ambient T h.empty h.maximal
    h.centralizing h.prepared.le_selected h.prepared.nontrivial h.prepared.normalized
    h.prepared.seed_span hH
  have hq := (source_chosen_equality_inputs h.ambient T h.empty h.maximal hH h.centralizing
    h.prepared.le_selected h.prepared.nontrivial h.prepared.normalized h.prepared.seed_span
    h.prepared.le_local h.prepared.quadratic_ratio).1
  have hnf := source_notFF_of_ratio_two d hq
  have hV := h.prepared.inside_core H hH
  let := source_elementary_span_of_notFF d hV hnf
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  let S := T.subtype hH.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le hH.1.1.2
  let A₀ := A.subgroupOf H
  have hUN : U ≤ pCore 2 H := by
    intro u hu
    obtain ⟨x, hx, he⟩ := span_le_right_core d hV hu
    exact H.subtype_injective he ▸ hx
  obtain ⟨D,hD,_hDN,hDn,hDq,hDA,hAD⟩ :=
    h.delta_quadratic_replacement_in_sylow hH hA hAT
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hcount : s.noncentralCount = 2 :=
    source_chosen_noncentral_count_two_from_source h.ambient T h.empty h.maximal hH
      h.centralizing h.prepared.le_selected h.prepared.nontrivial h.prepared.normalized
      h.prepared.seed_span h.prepared.le_local hV h.prepared.quadratic_ratio s
  have heq := source_sqtk_multiple_equalities d h.prepared.nontrivial hV
    (Chapter3.sqtk_of_mem_H h.ambient hH.1.1.1) hq S hS s (by omega) D hD hDq hDn
  have hfixed := fixed_centralizer_of_replacement U (pCore 2 H) A₀ D hUN hDA hAD heq.2.2.2.1
  apply le_antisymm (inf_le_inf_left _ (centralizer_le inf_le_left))
  intro v hv
  have hvH : v ∈ H := ((span_le_right_core d hV).trans (twoCore_le H)) hv.1
  have hv' : (⟨v,hvH⟩ : H) ∈ U ⊓ centralizer (A₀ ⊓ pCore 2 H : Subgroup H) := by
    refine ⟨hv.1, ?_⟩
    intro a ha
    exact Subtype.ext (hv.2 a ⟨ha.1, mem_map_of_mem H.subtype ha.2⟩)
  rw [← hfixed] at hv'
  refine ⟨hv.1, ?_⟩
  intro a ha
  exact congrArg H.subtype (hv'.2 ⟨a,hA.1.1 ha⟩ ha)
end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section02
open Subgroup Stellmacher ChosenGeometry Section01 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The fixed-centralizer identity for every member of the literal Delta family. -/
theorem ChosenSmallSource.delta_fixed
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) (hA : A ∈ delta H) :
    conjugateSpan H V ⊓ centralizer (A : Set G) =
      conjugateSpan H V ⊓ centralizer (A ⊓ twoCoreIn H : Subgroup G) := by
  let : IsElementaryAbelian 2 A := hA.1.2.1
  have hp : IsPGroup 2 (A.subgroupOf H) :=
    (IsElementaryAbelian.isPGroup 2 A).comap_subtype
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  let S := T.subtype hH.1.1.2
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H P S
  let e := MulAut.conj (g : G)
  have hPS : (P : Subgroup H).map (MulAut.conj g).toMonoidHom = S := by
    change ((g • P : Sylow 2 H) : Subgroup H) = _
    rw [hg]
  have hAT : A.map e.toMonoidHom ≤ (T : Subgroup G) := by
    have hm := map_mono (f := H.subtype) ((map_mono hP).trans hPS.le)
    rw [map_map,show H.subtype.comp (MulAut.conj g).toMonoidHom =
      e.toMonoidHom.comp H.subtype from rfl,
      ← map_map,map_subgroupOf_eq_of_le hA.1.1] at hm
    exact hm.trans_eq (map_subgroupOf_eq_of_le hH.1.1.2)
  have he := h.delta_fixed_in_sylow hH (delta_conjugate hA g.property) hAT
  have hU : (conjugateSpan H V).map e.toMonoidHom = conjugateSpan H V := by
    apply mem_normalizer_iff_map_conj_eq.mp
    rw [conjugateSpan_eq]
    exact le_normalizer_conjugateSpanBy V H g.property
  have hN : (twoCoreIn H).map e.toMonoidHom = twoCoreIn H :=
    mem_normalizer_iff_map_conj_eq.mp (twoCore_normalized H g.property)
  apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
  rw [Subgroup.map_inf _ _ _ e.injective,Subgroup.map_inf _ _ _ e.injective,
    Theory.GroupTheory.map_centralizer_equiv,Theory.GroupTheory.map_centralizer_equiv,hU]
  have hAN : (A ⊓ twoCoreIn H).map e.toMonoidHom = A.map e.toMonoidHom ⊓ twoCoreIn H := by
    rw [Subgroup.map_inf _ _ _ e.injective,hN]
  change conjugateSpan H V ⊓ centralizer (A.map e.toMonoidHom : Set G) =
    conjugateSpan H V ⊓ centralizer ((A ⊓ twoCoreIn H).map e.toMonoidHom : Set G)
  rw [hAN]
  exact he

/-- The actual difference of image families is inhabited without a uniform
chief-action callback. -/
theorem ChosenSmallSource.sigmaOutside_nonempty
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    (sigmaOutside (T : Subgroup G) H).Nonempty :=
  h.sigmaOutside_nonempty_of_uniform_fixed hH (fun _ hA => h.delta_fixed hH hA)
end CFSG.Quasithin.Chapter15.Section02
