module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointOddCore
public import CFSG.Quasithin.ChapterB.InternalThompsonAction
public import CFSG.Quasithin.ChapterF.Section06.Elementary.ActionPrimeComparison
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Subnormal
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Residual

/-!
# The literal complementary-point FF module in 13.2.12

Let W be the span of the original complementary point zv under the paired
point join J. In the two-core branch W is reduced. If its Thompson action
were trivial, the eight-element singular orbit span, contained in W⟨v⟩,
would lie in the four-element original fixed plane. Thus the faithful
conjugation action J/C_J(W) is an FF-module.

The actual natural-factor preimage in the first point group moves zv:
otherwise its Sylow-conjugate factors would all centralize z. The second
point residual moves zv by the singular-span order calculation. F.6.7--8
therefore bounds both local centralizer kernels and makes C_J(W) solvable.
F.6.11 identifies both local action images with their literal O₃′ quotient
images, preserving the quotient maps on every element.

SourceAssembly/PointModule applies this family to the universal terminal
argument. The F.6.18 model exclusions and full 13.2.7 remain with
qt-d-1367-assembly; the independent earlier-source discharge remains with
qt-d-1361-source. Source: Aschbacher--Smith 13.2.12, pp.882--883.
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

/-- The original Thompson subgroup moves the literal complementary-point span. -/
theorem point_span_thompson_moves
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {J : Subgroup G} (hBJ : ChapterB.baumann (T : Subgroup G) ≤ J)
    (hLJ : Lv L (markedV d.flag.flag.module) ≤ J)
    (hJv : J ≤ Gv (markedV d.flag.flag.module))
    (x : J) (hx : (x : G) = markedZ d.flag.flag.module * markedV d.flag.flag.module) :
    ¬ elementaryAbelianMaxJ ((ChapterB.baumann (T : Subgroup G)).subgroupOf J) ≤
      centralizer (conjugateSpanBy (zpowers x) ⊤ : Set J) := by
  let s := d.flag.flag.module
  let W := conjugateSpanBy (zpowers x) ⊤
  let U := W.map J.subtype ⊔ zpowers (markedV s)
  let : W.Normal := normalizer_eq_top_iff.mp
    (top_unique (le_normalizer_conjugateSpanBy (zpowers x) ⊤))
  have hJmap : (elementaryAbelianMaxJ ((ChapterB.baumann (T : Subgroup G)).subgroupOf J)).map
      J.subtype = elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le hBJ]
    exact elementaryAbelianMaxJ_eq_of_intermediate _ _
      (ChapterB.elementaryAbelianMaxJ_le_baumann _) inf_le_left
  intro hc
  have hWC : W.map J.subtype ≤ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    rintro w ⟨w,hw,rfl⟩ t ht
    rw [←hJmap] at ht
    obtain ⟨t,ht,rfl⟩ := ht
    exact congrArg J.subtype ((hc ht w hw).symm)
  have hvC : zpowers (markedV s) ≤ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
    zpowers_le.mpr (thompson_fixes_plane_of_omega_movement d hH hZ d.flag.flag.vector_mem)
  have hUC : U ≤ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := sup_le hWC hvC
  have hJN : J ≤ normalizer (U : Set G) := by
    apply le_trans (le_inf ?_ ?_) (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · apply le_normalizer_iff.mpr
      rintro g hg w ⟨w,hw,rfl⟩
      exact mem_map_of_mem J.subtype ((inferInstance : W.Normal).conj_mem w hw ⟨g,hg⟩)
    · have hh : J ≤ centralizer (zpowers (markedV s) : Set G) := by
        simpa only [zpowers_eq_closure,centralizer_closure] using
          (show J ≤ centralizer ({markedV s} : Set G) from hJv)
      exact hh.trans (Subgroup.centralizer_le_normalizer _)
  have hzU : markedZ s ∈ U := by
    apply (mul_mem_cancel_right (show markedV s ∈ U from mem_sup_right (mem_zpowers _))).mp
    rw [←hx]
    exact mem_sup_left (mem_map_of_mem J.subtype (le_conjugateSpanBy _ _ (mem_zpowers x)))
  have hspan : Vv L (markedZ s) (markedV s) ≤ U :=
    conjugateSpanBy_le (zpowers_le.mpr hzU) (hLJ.trans hJN)
  have hplane : Vv L (markedZ s) (markedV s) ≤ V₂ := by
    rw [←source_alpha_eq_flag_plane d hH hB hZ hs hz,
      source_alpha_eq_local_fixed_plane d hH hB hZ hs hz]
    exact le_inf (Vv_le_module s) (hspan.trans hUC)
  have hh := card_le_of_le hplane
  rw [Vv_card,d.flag.two_card] at hh
  omega

/-- The source core branch constructs a reduced FF module on the original quotient. -/
theorem point_overgroup_ff_span_of_complement_mem_core
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {J : Subgroup G} (hBJ : ChapterB.baumann (T : Subgroup G) ≤ J)
    (hLJ : Lv L (markedV d.flag.flag.module) ≤ J)
    (hJv : J ≤ Gv (markedV d.flag.flag.module))
    (he : markedZ d.flag.flag.module * markedV d.flag.flag.module ∈ J.pCoreIn 2) :
    ∃ x : J, (x : G) = markedZ d.flag.flag.module * markedV d.flag.flag.module ∧
      ∃ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
        letI := hr.normal
        letI := hr.elementary
        IsFFModule (ChapterB.InternalThompsonAction.action (conjugateSpanBy (zpowers x) ⊤)) := by
  obtain ⟨x,hx,hr⟩ := point_overgroup_reduced_span_of_complement_mem_core
    d hH hB hZ hs hz hBJ hJv he
  let W := conjugateSpanBy (zpowers x) ⊤
  let := hr.normal
  let := hr.elementary
  obtain ⟨S,hS⟩ := (point_baumann_sylow d hH hB hZ hs hz).restrict hBJ hJv
  have hSB : (S : Subgroup J) = (ChapterB.baumann (T : Subgroup G)).subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le hBJ]
  refine ⟨x,hx,hr,?_⟩
  exact NormalElementaryQuotient.isFFModule_of_thompson_not_le W
    (ChapterB.InternalThompsonAction.actionMk W) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) (S : Subgroup J)
    (hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S))
    (by simpa only [hSB,ChapterB.InternalThompsonAction.actionMk,QuotientGroup.ker_mk'] using
      point_span_thompson_moves d hH hB hZ hs hz hBJ hLJ hJv x hx)


omit d [Finite G] in
private theorem transitive_factor_preimage_le
    {Q E : Type*} [Group Q] [Finite Q] [AddCommGroup E] [Module (ZMod 2) E]
    (q : H →* Q) (hq : Function.Surjective q)
    (hTH : (T : Subgroup G) ≤ H)
    (hk : q.ker ≤ (T : Subgroup G).subgroupOf H)
    {ρ : Representation (ZMod 2) Q E} (c : ChapterB.SolvableFFFactors ρ)
    (ht : ∀ i j, ∃ t : T.subtype hTH,
      (c.factor i).map (MulAut.conj (q t)).toMonoidHom = c.factor j)
    (hgen : offenderSubgroup ρ ⊔ ((T : Subgroup G).subgroupOf H).map q = ⊤)
    (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (i : Fin c.count) (hi : ((c.factor i).comap q).map H.subtype ≤ M) : H ≤ M := by
  have hall (j : Fin c.count) : (c.factor j).comap q ≤ M.subgroupOf H := by
    obtain ⟨t,ht⟩ := ht i j
    intro x hx
    have hconj : q ((t : H)⁻¹ * x * t) ∈ c.factor i := by
      obtain ⟨y,hy,he⟩ := ht.symm ▸ hx
      have heq : (q t)⁻¹ * q x * q t = y := by
        rw [←he]
        simp [MulAut.conj_apply,mul_assoc]
      rw [map_mul,map_mul,map_inv,heq]
      exact hy
    have hm := hi (mem_map_of_mem H.subtype hconj)
    have htM : ((t : H) : G) ∈ M := hTM t.property
    have hh := M.mul_mem (M.mul_mem htM hm) (M.inv_mem htM)
    change ((t : H) : G) * (((t : H) : G)⁻¹ * (x : G) * (t : H)) *
      ((t : H) : G)⁻¹ ∈ M at hh
    change (x : G) ∈ M
    simpa only [mul_assoc,mul_inv_cancel_left,inv_mul_cancel_right,mul_inv_cancel,mul_one] using hh
  have hMker : q.ker ≤ M.subgroupOf H := hk.trans (comap_mono hTM)
  have hO : offenderSubgroup ρ ≤ (M.subgroupOf H).map q := by
    rw [←c.iSup_factor]
    apply iSup_le
    intro j
    rw [←map_comap_eq_self_of_surjective hq (c.factor j)]
    exact map_mono (hall j)
  have htop : (M.subgroupOf H).map q = ⊤ := by
    apply top_unique
    rw [←hgen]
    exact sup_le hO (map_mono (comap_mono hTM))
  have htopM : M.subgroupOf H = ⊤ := by
    rw [←comap_map_eq_self hMker,htop,comap_top]
  exact fun x hx => show x ∈ M from htopM.ge (mem_top (⟨x,hx⟩ : H))

/-- The first original point group moves the same complementary point.
This retains its literal natural-factor preimage and the original Sylow orbit. -/
theorem original_paired_point_not_centralizes_complement
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {P₁ : Subgroup G} (horiginal : IsOriginalPairedPointGroup d hH P₁)
    (hPv : P₁ ≤ Gv (markedV d.flag.flag.module)) :
    ¬ P₁ ≤ Gv (markedZ d.flag.flag.module * markedV d.flag.flag.module) := by
  let s := d.flag.flag.module
  let S := T.subtype hH.1.1.2
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  obtain ⟨c,_,ht,i,j,_,_,hP⟩ := horiginal
  obtain ⟨_,_,hp,_,hj⟩ := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
  have hne : q.ker ≠ ⊤ := by
    intro he
    apply hj
    rw [QuotientGroup.ker_mk'] at he
    exact le_top.trans he.ge
  have hpq := (ChapterB.minimalParabolic_reduced_image S hp q
    (QuotientGroup.mk'_surjective C) hU.quotient_pCore_eq_bot hne).2
  have hgen := (ChapterB.offender_generation (S.mapSurjective (QuotientGroup.mk'_surjective C))
    hpq ρ ((isFFModule_iff_quadraticRatio_le_one ρ).mpr c.ratio_one.le)
      hU.quotient_pCore_eq_bot).2
  have hk : q.ker ≤ (S : Subgroup H) := by
    rw [QuotientGroup.ker_mk']
    change centralizer ((omegaOrbit T H).subgroupOf H : Set H) ≤ _
    rw [source_omega_centralizer_eq_twoCore d hH hB hZ hs]
    exact pCore_isPGroup.le_sylow_of_normal S
  have hTz : (T : Subgroup G) ≤ Gv (markedZ s) := fun t ht =>
    mem_centralizer_singleton_iff.mpr
      (((mem_omegaOneCenterAmbient_iff _ _).mp d.flag.flag.z_central).2.2 t ht)
  intro he
  have hPz : P₁ ≤ Gv (markedZ s) := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    simpa only [mul_inv_cancel_right] using
      (Commute.mul_right (mem_centralizer_singleton_iff.mp (he ha))
        (Commute.inv_right (mem_centralizer_singleton_iff.mp (hPv ha)))).eq
  have hHz := transitive_factor_preimage_le q (QuotientGroup.mk'_surjective C) hH.1.1.2
    hk c.toSolvableFFFactors ht hgen (Gv (markedZ s)) hTz i
    ((hP ▸ le_sup_left).trans hPz)
  apply hZ
  rw [source_omegaCenter_eq_flag_line d hH hB hZ hs hz,←d.flag.flag.line_eq]
  simpa only [zpowers_eq_closure,centralizer_closure] using
    (show H ≤ centralizer ({markedZ s} : Set G) from hHz)

/-- The second original point residual moves the complementary point,
as otherwise its eight-element singular span would be a line. -/
theorem point_residual_not_centralizes_complement :
    ¬ Lv L (markedV d.flag.flag.module) ≤
      Gv (markedZ d.flag.flag.module * markedV d.flag.flag.module) := by
  let s := d.flag.flag.module
  intro he
  have hz : Lv L (markedV s) ≤ Gv (markedZ s) := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    have hv : a * markedV s = markedV s * a := mem_centralizer_singleton_iff.mp
      ((map_subtype_le _).trans inf_le_right ha)
    have hc : a * (markedZ s * markedV s) = (markedZ s * markedV s) * a :=
      mem_centralizer_singleton_iff.mp (he ha)
    simpa only [mul_inv_cancel_right] using (Commute.mul_right hc (Commute.inv_right hv)).eq
  have hn : Lv L (markedV s) ≤ normalizer (zpowers (markedZ s) : Set G) := by
    have hh : Lv L (markedV s) ≤ centralizer (zpowers (markedZ s) : Set G) := by
      simpa only [zpowers_eq_closure,centralizer_closure] using
        (show Lv L (markedV s) ≤ centralizer ({markedZ s} : Set G) from hz)
    exact hh.trans (Subgroup.centralizer_le_normalizer _)
  have hspan : Vv L (markedZ s) (markedV s) ≤ zpowers (markedZ s) :=
    conjugateSpanBy_le le_rfl hn
  have hcard := card_le_of_le hspan
  rw [Vv_card, d.flag.flag.line_eq,d.flag.one_card] at hcard
  omega


omit d in
private theorem goldschmidt_centralizer_local_bound
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (hg : ChapterF.IsGoldschmidtTriple A B) (W : Subgroup D) [W.Normal]
    (x : D) (hx : x ∈ W) (hcx : A ⊓ B ≤ centralizer ({x} : Set D))
    (hn : ¬ A ≤ centralizer ({x} : Set D)) :
    A ⊓ centralizer (W : Set D) ≤ A.pCoreIn 2 := by
  apply (hg.left_subnormal_core_iff_not_residual_le _
    (inferInstance : (centralizer (W : Set D)).Normal).isSubnormal).mpr
  intro hres
  apply hn
  rw [←hg.left_residual_sup_intersection]
  exact sup_le (hres.trans (centralizer_le (Set.singleton_subset_iff.mpr hx))) hcx

/-- Both local kernels of the literal conjugate-span action are two-groups.
Only normality of the span is needed; no F.6.18 row is assumed. -/
theorem point_span_local_kernel_bounds
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {P₁ : Subgroup G} (horiginal : IsOriginalPairedPointGroup d hH P₁)
    (hPv : P₁ ≤ Gv (markedV d.flag.flag.module))
    (hinter : P₁ ⊓ (Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)) =
      ChapterB.baumann (T : Subgroup G)) :
    let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    let J := P₁ ⊔ P₂
    let A := P₁.subgroupOf J
    let B := P₂.subgroupOf J
    ChapterF.IsGoldschmidtTriple A B →
    ∀ (x : J), (x : G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ W : Subgroup J, W.Normal → x ∈ W →
      A ⊓ centralizer (W : Set J) ≤ A.pCoreIn 2 ∧
      B ⊓ centralizer (W : Set J) ≤ B.pCoreIn 2 := by
  intro P₂ J A B hg x hx W hW hxW
  let := hW
  have hcx : A ⊓ B ≤ centralizer ({x} : Set J) := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    change (a:G) * (x:G) = (x:G) * (a:G)
    rw [hx]
    exact mem_centralizer_iff.mp (complement_centralizes_baumann d hH hB hZ hs hz)
      a (hinter ▸ ha)
  have hnA : ¬ A ≤ centralizer ({x} : Set J) := by
    intro hh
    apply original_paired_point_not_centralizes_complement d hH hB hZ hs hz horiginal hPv
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg J.subtype (mem_centralizer_singleton_iff.mp
      (hh (show (⟨a,mem_sup_left ha⟩ : J) ∈ A from ha)))
    change a * (x:G) = (x:G) * a at he
    rwa [hx] at he
  have hnB : ¬ B ≤ centralizer ({x} : Set J) := by
    intro hh
    apply point_residual_not_centralizes_complement d
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg J.subtype (mem_centralizer_singleton_iff.mp
      (hh (show (⟨a,mem_sup_right (mem_sup_left ha)⟩ : J) ∈ B from mem_sup_left ha)))
    change a * (x:G) = (x:G) * a at he
    rwa [hx] at he
  exact ⟨goldschmidt_centralizer_local_bound hg W x hxW hcx hnA,
    goldschmidt_centralizer_local_bound hg.symm W x hxW (inf_comm A B ▸ hcx) hnB⟩

/-- The action on the same reduced span has solvable kernel, and its two
local images identify with the literal O₃′ quotient images. Both maps are retained. -/
theorem point_span_action_comparison
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {P₁ : Subgroup G} (horiginal : IsOriginalPairedPointGroup d hH P₁)
    (hPv : P₁ ≤ Gv (markedV d.flag.flag.module))
    (hinter : P₁ ⊓ (Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)) =
      ChapterB.baumann (T : Subgroup G)) :
    let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    let J := P₁ ⊔ P₂
    let A := P₁.subgroupOf J
    let B := P₂.subgroupOf J
    ChapterF.IsGoldschmidtTriple A B →
    ∀ (x : J), (x : G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ (W : Subgroup J) (hr : IsPReduced 2 W),
      letI := hr.normal
      x ∈ W →
      let q := QuotientGroup.mk' (centralizer (W : Set J))
      let r := QuotientGroup.mk' (pPrimeCore 3 J)
      Group.IsSolvable (centralizer (W : Set J)) ∧
      (q.subgroupMap A).ker = (pCore 2 J).subgroupOf A ∧
      (q.subgroupMap B).ker = (pCore 2 J).subgroupOf B ∧
      ∃ eA : A.map q ≃* A.map r, ∃ eB : B.map q ≃* B.map r,
        (∀ a : A, eA (q.subgroupMap A a) = r.subgroupMap A a) ∧
        (∀ b : B, eB (q.subgroupMap B b) = r.subgroupMap B b) := by
  intro P₂ J A B hg x hx W hr
  let := hr.normal
  intro hxW q r
  obtain ⟨hA,hB'⟩ := point_span_local_kernel_bounds d hH hB hZ hs hz
    horiginal hPv hinter hg x hx W hr.normal hxW
  have hlocal (M : Subgroup J) (hm : M ⊓ centralizer (W : Set J) ≤ M.pCoreIn 2) :
      IsPGroup 2 (q.subgroupMap M).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    apply pCore_isPGroup.to_le
    intro a ha
    obtain ⟨a',ha',he⟩ := hm ⟨a.property,ha⟩
    exact (Subtype.ext he : a'=a) ▸ ha'
  have ha := hlocal A hA
  have hb := hlocal B hB'
  have hsol : Group.IsSolvable (centralizer (W : Set J)) := by
    have hh := hg.action_kernel_solvable q ha hb
    rwa [QuotientGroup.ker_mk'] at hh
  exact ⟨hsol,
    hg.action_kernel_on_vertex q (QuotientGroup.mk'_surjective _) hr.quotient_pCore_eq_bot ha hb A le_rfl,
    hg.symm.action_kernel_on_vertex q (QuotientGroup.mk'_surjective _) hr.quotient_pCore_eq_bot hb ha B le_rfl,
    hg.action_prime_local_equiv q (QuotientGroup.mk'_surjective _) hr.quotient_pCore_eq_bot ha hb A le_rfl,
    hg.symm.action_prime_local_equiv q (QuotientGroup.mk'_surjective _) hr.quotient_pCore_eq_bot hb ha B le_rfl,
    hg.action_prime_local_equiv_apply q (QuotientGroup.mk'_surjective _) hr.quotient_pCore_eq_bot ha hb A le_rfl,
    hg.symm.action_prime_local_equiv_apply q (QuotientGroup.mk'_surjective _) hr.quotient_pCore_eq_bot hb ha B le_rfl⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
