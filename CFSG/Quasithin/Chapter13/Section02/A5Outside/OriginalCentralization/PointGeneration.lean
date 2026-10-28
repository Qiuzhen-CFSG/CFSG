module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointModule
public import Theory.GroupTheory.SymmetricThreeThompsonSeed
public import CFSG.Quasithin.ChapterB.Section02.RelativeThompsonFactors

/-!
# Offender generation on the original paired-point action

The original complementary point lies in the central omega subgroup of the
common Thompson subgroup. Both vertices move it. If either local two-core
contained that Thompson subgroup, S₃ normal generation would force its
vertex to fix the point. Thus both local two-residuals lie in every normal
subgroup containing the common Thompson subgroup, by F.6.7.

B.2.10 puts the literal Thompson image in the normal offender subgroup of
the reduced full-span action. F.6.6 now places its full two-residual there,
so the quotient by the offender subgroup is a two-group. The original point,
span, inclusions and centralizer quotient are retained throughout.

Source: Aschbacher--Smith 13.2.12, printed p.882; B.2.10 and F.6.6--7.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section06.CentralizerReduction Section06.CentralizerReduction.A5Module
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

private theorem point_vertex_thompson_not_le_core
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    (P : Subgroup G) (hBP : ChapterB.baumann (T : Subgroup G) ≤ P)
    (hPv : P ≤ Gv (markedV d.flag.flag.module))
    (he : Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)))
    (hm : ¬ P ≤ Gv (markedZ d.flag.flag.module * markedV d.flag.flag.module)) :
    ¬ elementaryAbelianMaxJ (ChapterB.baumann (T : Subgroup G)) ≤ P.pCoreIn 2 := by
  let B := ChapterB.baumann (T : Subgroup G)
  obtain ⟨S,hS⟩ := (point_baumann_sylow d hH hB hZ hs hz).restrict hBP hPv
  have hj : (elementaryAbelianMaxJ (S : Subgroup P)).map P.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective P.subtype P.subtype_injective,hS]
    exact elementaryAbelianMaxJ_eq_of_intermediate _ _
      (ChapterB.elementaryAbelianMaxJ_le_baumann _) inf_le_left
  have hE : (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup P))).map
      P.subtype = V₂ := by
    rw [←omegaOneCenterAmbient_map_injective P.subtype P.subtype_injective,hj]
    exact source_alpha_eq_flag_plane d hH hB hZ hs hz
  have hV₂B : V₂ ≤ B := by
    rw [←source_alpha_eq_flag_plane d hH hB hZ hs hz]
    rw [←ChapterB.omegaCenter_baumann_eq_thompsonAlpha]
    exact fun x hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
  have hzV₂ : markedZ d.flag.flag.module ∈ V₂ := by
    apply d.flag.one_le_two
    exact d.flag.flag.line_eq.le (mem_zpowers _)
  let x : P := ⟨markedZ d.flag.flag.module * markedV d.flag.flag.module,
    hBP (hV₂B (V₂.mul_mem hzV₂ d.flag.flag.vector_mem))⟩
  have hx : x ∈ omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup P)) := by
    have hh : (x:G) ∈ (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup P))).map
        P.subtype := hE.symm ▸ V₂.mul_mem hzV₂ d.flag.flag.vector_mem
    exact (mem_map_iff_mem P.subtype_injective).mp hh
  have hfix : (S : Subgroup P) ≤ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup P)) : Set P) := by
    intro t ht w hw
    apply Subtype.ext
    have htB : (t:G) ∈ B := hS.le (mem_map_of_mem P.subtype ht)
    have hwE : (w:G) ∈ ChapterB.thompsonAlpha (T : Subgroup G) := by
      rw [source_alpha_eq_flag_plane d hH hB hZ hs hz,←hE]
      exact mem_map_of_mem P.subtype hw
    exact htB.2 w hwE
  have hmove : x ∉ center P := by
    intro hxC
    apply hm
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg P.subtype (mem_center_iff.mp hxC ⟨a,ha⟩)
  intro hle
  apply SymmetricThreeSeed.thompson_not_le_core_of_moved_alpha S he.some hfix x hx hmove
  intro t ht
  have hh : (t:G) ∈ P.pCoreIn 2 := hle (by
    rw [←hS,elementaryAbelianMaxJ_map_injective P.subtype P.subtype_injective]
    exact mem_map_of_mem P.subtype ht)
  exact (mem_map_iff_mem P.subtype_injective).mp hh

/-- Both literal point vertices have Thompson elements outside their two-cores. -/
theorem point_thompson_not_le_local_cores
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {P₁ : Subgroup G} (horiginal : IsOriginalPairedPointGroup d hH P₁)
    (hBP : ChapterB.baumann (T : Subgroup G) ≤ P₁)
    (hPv : P₁ ≤ Gv (markedV d.flag.flag.module)) :
    let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    let J := P₁ ⊔ P₂
    ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) →
    (¬ elementaryAbelianMaxJ (ChapterB.baumann (T : Subgroup G)) ≤ P₁.pCoreIn 2) ∧
    (¬ elementaryAbelianMaxJ (ChapterB.baumann (T : Subgroup G)) ≤ P₂.pCoreIn 2) := by
  intro P₂ J hg
  have hBv : ChapterB.baumann (T : Subgroup G) ≤ Gv (markedV d.flag.flag.module) :=
    (source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz _
      d.flag.flag.vector_mem d.flag.flag.vector_not_mem).le.trans inf_le_right
  have h₂v : P₂ ≤ Gv (markedV d.flag.flag.module) :=
    sup_le ((map_subtype_le _).trans inf_le_right) hBv
  have he (P : Subgroup G) (hPJ : P ≤ J)
      (he : Nonempty ((P.subgroupOf J ⧸ pCore 2 (P.subgroupOf J)) ≃* Equiv.Perm (Fin 3))) :
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) := by
    let e := subgroupOfEquivOfLe hPJ
    exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans he.some⟩
  refine ⟨point_vertex_thompson_not_le_core d hH hB hZ hs hz P₁ hBP hPv
    (he P₁ le_sup_left hg.quotient_left)
    (original_paired_point_not_centralizes_complement d hH hB hZ hs hz horiginal hPv),?_⟩
  apply point_vertex_thompson_not_le_core d hH hB hZ hs hz P₂ le_sup_right h₂v
    (he P₂ le_sup_right hg.quotient_right)
  exact fun hh => point_residual_not_centralizes_complement d (le_sup_left.trans hh)

/-- The actual two-residual lies in the normal offender subgroup. Consequently
the quotient by that subgroup is a two-group, without identifying the two groups. -/
theorem point_action_residual_le_offender
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {P₁ : Subgroup G} (horiginal : IsOriginalPairedPointGroup d hH P₁)
    (hBP : ChapterB.baumann (T : Subgroup G) ≤ P₁)
    (hPv : P₁ ≤ Gv (markedV d.flag.flag.module))
    (hinter : P₁ ⊓ (Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)) =
      ChapterB.baumann (T : Subgroup G)) :
    let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    let J := P₁ ⊔ P₂
    ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) →
    ∀ (x : J), (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
      letI := hr.normal
      letI := hr.elementary
      let W := conjugateSpanBy (zpowers x) ⊤
      let ρ := ChapterB.InternalThompsonAction.action W
      let N := offenderSubgroup ρ
      letI := offenderSubgroup_normal ρ
      pResidual 2 (J ⧸ centralizer (W : Set J)) ≤ N ∧
        IsPGroup 2 ((J ⧸ centralizer (W : Set J)) ⧸ N) := by
  intro P₂ J hg x hx hr
  let := hr.normal
  let := hr.elementary
  intro W ρ N
  let : N.Normal := offenderSubgroup_normal ρ
  let f := QuotientGroup.mk' (centralizer (W : Set J))
  let R := (ChapterB.baumann (T : Subgroup G)).subgroupOf J
  let C := N.comap f
  have hBJ : ChapterB.baumann (T : Subgroup G) ≤ J := hBP.trans le_sup_left
  have hKJ : Lv L (markedV d.flag.flag.module) ≤ J := le_sup_left.trans le_sup_right
  have hJv : J ≤ Gv (markedV d.flag.flag.module) := sup_le hPv (sup_le
    ((map_subtype_le _).trans inf_le_right)
    ((source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz _
      d.flag.flag.vector_mem d.flag.flag.vector_not_mem).le.trans inf_le_right))
  obtain ⟨S,hS⟩ := (point_baumann_sylow d hH hB hZ hs hz).restrict hBJ hJv
  have hSR : (S : Subgroup J) = R := by
    apply map_injective J.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le hBJ]
  have hWR : W ≤ R := hr.le_pCore.trans
    ((pCore_isPGroup.le_sylow_of_normal S).trans hSR.le)
  have hmove : ¬ elementaryAbelianMaxJ R ≤ f.ker := by
    simpa only [f,QuotientGroup.ker_mk'] using
      point_span_thompson_moves d hH hB hZ hs hz hBJ hKJ hJv x hx
  have hJC : elementaryAbelianMaxJ R ≤ C := by
    apply map_le_iff_le_comap.mp
    have hh := (ChapterB.lemma_B_2_10_relative W R hWR f
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hmove).2.2
    rw [←ChapterB.relative_thompson_span_image W R hWR f
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hmove] at hh
    exact (map_mono (le_conjugateSpanBy _ _)).trans hh
  have hn := point_thompson_not_le_local_cores d hH hB hZ hs hz horiginal hBP hPv hg
  have hi : P₁.subgroupOf J ⊓ P₂.subgroupOf J = R := by
    change (P₁ ⊓ P₂).subgroupOf J = R
    rw [hinter]
  have hnot (P : Subgroup G) (hPJ : P ≤ J)
      (hh : ¬ elementaryAbelianMaxJ (ChapterB.baumann (T : Subgroup G)) ≤ P.pCoreIn 2) :
      ¬ elementaryAbelianMaxJ R ≤ (P.subgroupOf J).pCoreIn 2 := by
    intro hle
    apply hh
    have hm := map_mono (f := J.subtype) hle
    rw [←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le hBJ,map_pCoreIn_of_injective _ _ _ J.subtype_injective,
      map_subgroupOf_eq_of_le hPJ] at hm
    exact hm
  have hleft : (pResidual 2 (P₁.subgroupOf J)).map (P₁.subgroupOf J).subtype ≤ C := by
    by_contra hh
    have hcore := (hg.left_subnormal_core_iff_not_residual_le C
      (inferInstance : C.Normal).isSubnormal).mpr hh
    exact hnot P₁ le_sup_left hn.1 ((le_inf
      ((show elementaryAbelianMaxJ R ≤ R from sSup_le fun _ hA => hA.1).trans (hi ▸ inf_le_left)) hJC).trans hcore)
  have hright : (pResidual 2 (P₂.subgroupOf J)).map (P₂.subgroupOf J).subtype ≤ C := by
    by_contra hh
    have hcore := (hg.right_subnormal_core_iff_not_residual_le C
      (inferInstance : C.Normal).isSubnormal).mpr hh
    exact hnot P₂ le_sup_right hn.2 ((le_inf
      ((show elementaryAbelianMaxJ R ≤ R from sSup_le fun _ hA => hA.1).trans (hi ▸ inf_le_right)) hJC).trans hcore)
  have hres : pResidual 2 J ≤ C := by
    rw [hg.twoResidual_eq_sup]
    exact sup_le hleft hright
  have him : pResidual 2 (J ⧸ centralizer (W : Set J)) ≤ N := by
    rw [←map_pResidual_of_surjective 2 f (QuotientGroup.mk'_surjective _)]
    exact map_le_iff_le_comap.mpr hres
  exact ⟨him,(pResidual_le_iff_isPGroup_quotient 2 N).mp him⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
