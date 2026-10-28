module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SolvableRow
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointSupport
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.NormalCubicSupport
public import CFSG.Quasithin.ChapterB.Section02.RelativeThompsonFactors
public import Theory.GroupTheory.ConjugateSpanCentralizingImage
public import Theory.GroupTheory.PResidual.AbelianNormality
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.AbelianSylowNormalFactors

/-!
# Excluding the solvable F.6 models on the original point span

The original Thompson subgroup moves the complementary point's local
four-group. Quotient centralization would propagate its fixation of the
point to that entire local span, so the actual offender subgroup moves
the second residual image. If that image is normal, its local kernel and
the reduced action show it has order three. Solvable FF theory bounds its
moved support by four, contradicting the larger full point-join span.

The source three-rank bound limits the solvable FF factor family to two.
If the action's Sylow two-subgroup is abelian, both factors are normal,
forcing the moving second residual image to be normal as well. This
excludes abelian Sylow subgroups in the solvable action. The established
local comparison transports this obstruction only on the actual common
Sylow images to the O₃′ quotient. Both models of F.6.18(2) are therefore
excluded, without identifying the two different ambient quotients.

SourceAssembly/PointSolvable applies these facts after every Sylow rechoice.
The nonsolvable F.6 comparison, generation bound and single-factor endgame
remain separate obligations. This does not yet prove original 13.2.7.

Source: Aschbacher--Smith 13.2.12, printed p.882; B.1.8 and F.6.18(2).
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

/-- The original Thompson subgroup moves even the local complementary plane. -/
theorem complement_span_thompson_moves
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (complementSpan d.flag.flag.module : Set G) := by
  let s := d.flag.flag.module
  let K := Lv L (markedV s)
  let W := complementSpan s
  let U := W ⊔ zpowers (markedV s)
  intro hc
  have hUC : U ≤ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
    sup_le (le_centralizer_iff.mp hc)
      (zpowers_le.mpr (thompson_fixes_plane_of_omega_movement d hH hZ d.flag.flag.vector_mem))
  have hn : K ≤ normalizer (U : Set G) := by
    apply le_trans (le_inf (le_normalizer_conjugateSpanBy _ _) ?_)
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
    have hh : K ≤ centralizer (zpowers (markedV s) : Set G) := by
      simpa only [zpowers_eq_closure,centralizer_closure,Gv] using
        (show K ≤ Gv (markedV s) from (map_subtype_le _).trans inf_le_right)
    exact hh.trans (Subgroup.centralizer_le_normalizer _)
  have hzU : markedZ s ∈ U := by
    apply (mul_mem_cancel_right (show markedV s ∈ U from mem_sup_right (mem_zpowers _))).mp
    exact mem_sup_left (le_conjugateSpanBy _ _ (mem_zpowers _))
  have hspan : Vv L (markedZ s) (markedV s) ≤ U :=
    conjugateSpanBy_le (zpowers_le.mpr hzU) hn
  have hplane : Vv L (markedZ s) (markedV s) ≤ V₂ := by
    rw [←source_alpha_eq_flag_plane d hH hB hZ hs hz,
      source_alpha_eq_local_fixed_plane d hH hB hZ hs hz]
    exact le_inf (Vv_le_module s) (hspan.trans hUC)
  have hh := card_le_of_le hplane
  rw [Vv_card,d.flag.two_card] at hh
  omega

/-- The same Thompson image does not centralize the second residual image. -/
theorem point_residual_image_thompson_moves
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {J : Subgroup G} (hBJ : ChapterB.baumann (T : Subgroup G) ≤ J)
    (hKJ : Lv L (markedV d.flag.flag.module) ≤ J)
    (x : J) (hx : (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module)
    (W : Subgroup J) [W.Normal] (hxW : x ∈ W) :
    let f := QuotientGroup.mk' (centralizer (W : Set J))
    let R := elementaryAbelianMaxJ ((ChapterB.baumann (T : Subgroup G)).subgroupOf J)
    let K := (Lv L (markedV d.flag.flag.module)).subgroupOf J
    ¬ R.map f ≤ centralizer (K.map f : Set _) := by
  intro f R K hc
  have hRmap : R.map J.subtype = elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le hBJ]
    exact elementaryAbelianMaxJ_eq_of_intermediate _ _
      (ChapterB.elementaryAbelianMaxJ_le_baumann _) inf_le_left
  have hfix : R ≤ centralizer (zpowers x : Set J) := by
    rw [zpowers_eq_closure,centralizer_closure]
    intro r hr
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    change (r:G)*(x:G)=(x:G)*(r:G)
    rw [hx]
    exact mem_centralizer_iff.mp (complement_centralizes_baumann d hH hB hZ hs hz)
      r (((ChapterB.elementaryAbelianMaxJ_le_baumann ((ChapterB.baumann (T : Subgroup G)).subgroupOf J)).trans inf_le_left) hr)
  have hk : f.ker ≤ centralizer (zpowers x : Set J) := by
    rw [QuotientGroup.ker_mk']
    exact centralizer_le (zpowers_le.mpr hxW)
  have hh := centralizes_span_of_centralizing_images f R K (zpowers x) hfix hk hc
  apply complement_span_thompson_moves d hH hB hZ hs hz
  have hm : (conjugateSpanBy (zpowers x) K).map J.subtype = complementSpan d.flag.flag.module := by
    rw [map_conjugateSpanBy,MonoidHom.map_zpowers,map_subgroupOf_eq_of_le hKJ]
    change conjugateSpanBy (zpowers (x:G)) (Lv L (markedV d.flag.flag.module)) = _
    rw [hx]
    rfl
  intro r hr w hw
  rw [←hRmap] at hr
  rw [←hm] at hw
  obtain ⟨r,hr,rfl⟩ := hr
  obtain ⟨w,hw,rfl⟩ := hw
  exact congrArg J.subtype (hh hr w hw)

/-- The full offender subgroup moves the actual second residual image. -/
theorem point_residual_image_offenders_move
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {J : Subgroup G} (hBJ : ChapterB.baumann (T : Subgroup G) ≤ J)
    (hKJ : Lv L (markedV d.flag.flag.module) ≤ J)
    (hJv : J ≤ Gv (markedV d.flag.flag.module))
    (x : J) (hx : (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module)
    (hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤)) :
    letI := hr.normal
    letI := hr.elementary
    let W := conjugateSpanBy (zpowers x) ⊤
    let f := QuotientGroup.mk' (centralizer (W : Set J))
    let K := (Lv L (markedV d.flag.flag.module)).subgroupOf J
    ¬ offenderSubgroup (ChapterB.InternalThompsonAction.action W) ≤ centralizer (K.map f : Set _) := by
  let := hr.normal
  let := hr.elementary
  intro W f K
  let ρ := ChapterB.InternalThompsonAction.action W
  let R := (ChapterB.baumann (T : Subgroup G)).subgroupOf J
  have hmove := point_span_thompson_moves d hH hB hZ hs hz hBJ hKJ hJv x hx
  have hmove' : ¬ elementaryAbelianMaxJ R ≤ f.ker := by
    simpa only [f,QuotientGroup.ker_mk'] using hmove
  obtain ⟨S,hS⟩ := (point_baumann_sylow d hH hB hZ hs hz).restrict hBJ hJv
  have hRS : (S : Subgroup J) = R := by
    apply map_injective J.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le hBJ]
  have hWR : W ≤ R := hr.le_pCore.trans
    ((pCore_isPGroup.le_sylow_of_normal S).trans hRS.le)
  have hJR : (elementaryAbelianMaxJ R).map f ≤ offenderSubgroup ρ := by
    have hh := (ChapterB.lemma_B_2_10_relative W R hWR f
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hmove').2.2
    have hspan := ChapterB.relative_thompson_span_image W R hWR f
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hmove'
    rw [←hspan] at hh
    exact (map_mono (le_conjugateSpanBy _ _)).trans hh
  intro hc
  exact point_residual_image_thompson_moves d hH hB hZ hs hz hBJ hKJ x hx W
    (le_conjugateSpanBy _ _ (mem_zpowers x)) (hJR.trans hc)

/-- A normal second-residual image in the reduced action is literally cubic.
Its two-core is normal in the ambient core-free action, and the original
local kernel is a two-group. -/
theorem point_normal_residual_image_card
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
    ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) →
    ∀ (x : J), (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
      letI := hr.normal
      let W := conjugateSpanBy (zpowers x) ⊤
      let K := (Lv L (markedV d.flag.flag.module)).subgroupOf J
      let f := QuotientGroup.mk' (centralizer (W : Set J))
      (K.map f).Normal → Nat.card (K.map f) = 3 := by
  intro P₂ J hg x hx hr
  let := hr.normal
  intro W K f hn
  let := hn
  have hKJ : Lv L (markedV d.flag.flag.module) ≤ J := le_sup_left.trans le_sup_right
  have hQ : pCore 2 (K.map f) = ⊥ := by
    apply bot_unique
    intro a ha
    have hh := pCoreIn_le_of_subnormal 2 hn.isSubnormal (mem_map_of_mem (K.map f).subtype ha)
    rw [hr.quotient_pCore_eq_bot] at hh
    exact Subtype.ext (mem_bot.mp hh)
  obtain ⟨_,_,hb,_⟩ := point_span_action_comparison d hH hB hZ hs hz horiginal
    hPv hinter hg x hx W hr (le_conjugateSpanBy _ _ (mem_zpowers x))
  have hk : IsPGroup 2 (f.subgroupMap K).ker := by
    apply (pCore_isPGroup (p := 2) (G := J)).comap_subtype.to_le
    intro a ha
    have hh : (⟨a,mem_sup_left a.property⟩ : P₂.subgroupOf J) ∈
        (f.subgroupMap (P₂.subgroupOf J)).ker := by
      have hh : f (a:J) = 1 := congrArg (fun y : K.map f => (y : J ⧸ centralizer (W : Set J))) ha
      exact Subtype.ext hh
    rw [hb] at hh
    exact hh
  let e := subgroupOfEquivOfLe hKJ
  have hc : Nat.card (K ⧸ pCore 2 K) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
    exact d.flag.flag.residualQuotient_card
  rw [Nat.card_congr ((f.subgroupMap K).pCoreQuotientEquiv
    (f.subgroupMap_surjective K) hk).toEquiv,hQ,
    Nat.card_congr QuotientGroup.quotientBot.toEquiv] at hc
  exact hc

/-- Solvability of the actual FF action excludes normality of the second
residual image. B.1.8 bounds its moved support by four, whereas the literal
normal commutator contains the seed and thus fills the larger full span. -/
theorem point_solvable_action_not_normal_residual_image
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
    ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) →
    P₁.pCoreIn 2 ≠ P₂.pCoreIn 2 →
    ∀ (x : J), (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
      letI := hr.normal
      letI := hr.elementary
      let W := conjugateSpanBy (zpowers x) ⊤
      let K := (Lv L (markedV d.flag.flag.module)).subgroupOf J
      let f := QuotientGroup.mk' (centralizer (W : Set J))
      IsFFModule (ChapterB.InternalThompsonAction.action W) →
      Group.IsSolvable (J ⧸ centralizer (W : Set J)) → ¬ (K.map f).Normal := by
  intro P₂ J hg hne x hx hr
  let := hr.normal
  let := hr.elementary
  intro W K f hff hsol hn
  let := hn
  let ρ := ChapterB.InternalThompsonAction.action W
  let R := (ChapterB.baumann (T : Subgroup G)).subgroupOf J
  have hBJ : ChapterB.baumann (T : Subgroup G) ≤ J := le_sup_right.trans le_sup_right
  have hKJ : Lv L (markedV d.flag.flag.module) ≤ J := le_sup_left.trans le_sup_right
  have hJv : J ≤ Gv (markedV d.flag.flag.module) := sup_le hPv (sup_le
    ((map_subtype_le _).trans inf_le_right)
    ((source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz _
      d.flag.flag.vector_mem d.flag.flag.vector_not_mem).le.trans inf_le_right))
  have hm := point_residual_image_offenders_move d hH hB hZ hs hz hBJ hKJ hJv x hx hr
  have hc := point_normal_residual_image_card d hH hB hZ hs hz horiginal hPv hinter hg x hx hr hn
  have hsmall := ChapterB.normal_cubic_moved_card_le_four hsol hr.quotient_pCore_eq_bot
    (NormalElementaryQuotient.representation_injective W f
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) hff (K.map f) hc hm
  have hlarge := (point_moved_support_gt_four_of_normal_image d hH hB hZ hs hz
    horiginal hPv hinter hg hne x hx hr hn).2
  exact (not_lt_of_ge hsmall) hlarge

/-- The actual faithful point-span action has nonabelian two-residual.
This excludes the symmetric-three square on that action, using the source
Sylow normalization rather than identifying the two different quotients. -/
theorem point_action_residual_not_abelian
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
    ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) →
    P₁.pCoreIn 2 ≠ P₂.pCoreIn 2 →
    ∀ (x : J), (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
      letI := hr.normal
      letI := hr.elementary
      let W := conjugateSpanBy (zpowers x) ⊤
      IsFFModule (ChapterB.InternalThompsonAction.action W) →
      ¬ IsMulCommutative (pResidual 2 (J ⧸ centralizer (W : Set J))) := by
  intro P₂ J hg hne x hx hr
  let := hr.normal
  let := hr.elementary
  intro W hff hab
  let := hab
  let D := J ⧸ centralizer (W : Set J)
  let f := QuotientGroup.mk' (centralizer (W : Set J))
  let K := (Lv L (markedV d.flag.flag.module)).subgroupOf J
  have hBJ : ChapterB.baumann (T : Subgroup G) ≤ J := le_sup_right.trans le_sup_right
  have hKJ : Lv L (markedV d.flag.flag.module) ≤ J := le_sup_left.trans le_sup_right
  have hJv : J ≤ Gv (markedV d.flag.flag.module) := sup_le hPv (sup_le
    ((map_subtype_le _).trans inf_le_right)
    ((source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz _
      d.flag.flag.vector_mem d.flag.flag.vector_not_mem).le.trans inf_le_right))
  obtain ⟨S,hS⟩ := (point_baumann_sylow d hH hB hZ hs hz).restrict hBJ hJv
  have hSK : (S : Subgroup J) ≤ normalizer (K : Set J) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro k
    exact mem_normalizer_iff.mp (point_residual_normalized_by_baumann d hH hB hZ hs hz
      (hS ▸ mem_map_of_mem J.subtype ht)) (k:G)
  have hp : IsPPerfect 2 K := (isPPerfect_embedded_pResidual 2
    (L ⊓ Gv (markedV d.flag.flag.module))).of_surjective
      (subgroupOfEquivOfLe hKJ).symm.toMonoidHom (subgroupOfEquivOfLe hKJ).symm.surjective
  have hpimage : IsPPerfect 2 (K.map f) := hp.of_surjective
    (f.subgroupMap K) (f.subgroupMap_surjective K)
  have hn := normal_of_pPerfect_of_abelian_residual
    (S.mapSurjective (QuotientGroup.mk'_surjective _)) (K.map f) hpimage
    ((map_mono hSK).trans (K.le_normalizer_map f))
  let : Group.IsNilpotent (D ⧸ pResidual 2 D) := (isPGroup_quotient_pResidual 2).isNilpotent
  have hsol : Group.IsSolvable D := (Group.isSolvable_iff_subgroup_quotient (pResidual 2 D)).mpr
    ⟨inferInstance,inferInstance⟩
  exact point_solvable_action_not_normal_residual_image d hH hB hZ hs hz horiginal hPv
    hinter hg hne x hx hr hff hsol hn

/-- A solvable faithful point action cannot have abelian Sylow two-subgroups.
The original rank bound limits the natural factor family to two; Sylow
commutativity makes those factors normal and forces normality of the
moving original cubic image, which has already been excluded. -/
theorem point_solvable_action_sylow_not_abelian
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
    ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) →
    P₁.pCoreIn 2 ≠ P₂.pCoreIn 2 →
    primeRank 3 J ≤ 2 →
    ∀ (x : J), (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
      letI := hr.normal
      letI := hr.elementary
      let W := conjugateSpanBy (zpowers x) ⊤
      let f := QuotientGroup.mk' (centralizer (W : Set J))
      IsFFModule (ChapterB.InternalThompsonAction.action W) →
      Group.IsSolvable (J ⧸ centralizer (W : Set J)) →
      ¬ IsMulCommutative (((ChapterB.baumann (T : Subgroup G)).subgroupOf J).map f) := by
  intro P₂ J hg hne hrank x hx hr
  let := hr.normal
  let := hr.elementary
  intro W f hff hsol hab
  let := hab
  let K := (Lv L (markedV d.flag.flag.module)).subgroupOf J
  let ρ := ChapterB.InternalThompsonAction.action W
  have hBJ : ChapterB.baumann (T : Subgroup G) ≤ J := le_sup_right.trans le_sup_right
  have hKJ : Lv L (markedV d.flag.flag.module) ≤ J := le_sup_left.trans le_sup_right
  have hJv : J ≤ Gv (markedV d.flag.flag.module) := sup_le hPv (sup_le
    ((map_subtype_le _).trans inf_le_right)
    ((source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz _
      d.flag.flag.vector_mem d.flag.flag.vector_not_mem).le.trans inf_le_right))
  obtain ⟨S,hS⟩ := (point_baumann_sylow d hH hB hZ hs hz).restrict hBJ hJv
  have hSK : (S : Subgroup J) ≤ normalizer (K : Set J) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro k
    exact mem_normalizer_iff.mp (point_residual_normalized_by_baumann d hH hB hZ hs hz
      (hS ▸ mem_map_of_mem J.subtype ht)) (k:G)
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective (centralizer (W : Set J)))
  have hS' : IsMulCommutative S' := by
    have he : (S : Subgroup J) = (ChapterB.baumann (T : Subgroup G)).subgroupOf J := by
      apply map_injective J.subtype_injective
      rw [hS,map_subgroupOf_eq_of_le hBJ]
    change IsMulCommutative ((S : Subgroup J).map f)
    rwa [he]
  have hp : IsPPerfect 2 K := (isPPerfect_embedded_pResidual 2
    (L ⊓ Gv (markedV d.flag.flag.module))).of_surjective
      (subgroupOfEquivOfLe hKJ).symm.toMonoidHom (subgroupOfEquivOfLe hKJ).symm.surjective
  have hpimage : IsPPerfect 2 (K.map f) := hp.of_surjective
    (f.subgroupMap K) (f.subgroupMap_surjective K)
  have hcard : ∃ n, Nat.card (K.map f) ∣ 3 * 2 ^ n := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := Lv L (markedV d.flag.flag.module))).exists_card_eq
    have hc := card_eq_card_quotient_mul_card_subgroup (pCore 2 (Lv L (markedV d.flag.flag.module)))
    rw [d.flag.flag.residualQuotient_card,hn] at hc
    refine ⟨n,?_⟩
    have hh := card_map_dvd (f := f) (H := K)
    rw [Nat.card_congr (subgroupOfEquivOfLe hKJ).toEquiv,hc] at hh
    exact hh
  obtain ⟨c⟩ := ChapterB.solvableFFStructure_nonempty ρ hsol hr.quotient_pCore_eq_bot
    (NormalElementaryQuotient.representation_injective W f
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) hff
  have hn := c.toSolvableFFFactors.cubic_normal_of_abelian_sylow
    (c.toSolvableFFFactors.count_le_two_of_surjective_threeRank f
      (QuotientGroup.mk'_surjective _) hrank) S' hS' (K.map f) hpimage
    ((map_mono hSK).trans (K.le_normalizer_map f)) hcard
    (point_residual_image_offenders_move d hH hB hZ hs hz hBJ hKJ hJv x hx hr)
  exact point_solvable_action_not_normal_residual_image d hH hB hZ hs hz horiginal hPv
    hinter hg hne x hx hr hff hsol hn

/-- The solvable O₃′ quotient in the original paired point amalgam cannot
have abelian Sylow two-subgroups. Both quotient maps are retained, and the
comparison is only on their literal common Sylow images. -/
theorem point_solvable_quotient_sylow_not_abelian
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
    ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) →
    P₁.pCoreIn 2 ≠ P₂.pCoreIn 2 →
    primeRank 3 J ≤ 2 →
    ∀ (x : J), (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
      letI := hr.normal
      letI := hr.elementary
      let W := conjugateSpanBy (zpowers x) ⊤
      let q := QuotientGroup.mk' (pPrimeCore 3 J)
      IsFFModule (ChapterB.InternalThompsonAction.action W) →
      Group.IsSolvable (J ⧸ pPrimeCore 3 J) →
      ¬ IsMulCommutative (((ChapterB.baumann (T : Subgroup G)).subgroupOf J).map q) := by
  intro P₂ J hg hne hrank x hx hr
  let := hr.normal
  let := hr.elementary
  intro W q hff hsol hab
  let := hab
  let R := (ChapterB.baumann (T : Subgroup G)).subgroupOf J
  let A := P₁.subgroupOf J
  let B := P₂.subgroupOf J
  let f := QuotientGroup.mk' (centralizer (W : Set J))
  obtain ⟨_,ha,hb,_⟩ := point_span_action_comparison d hH hB hZ hs hz horiginal
    hPv hinter hg x hx W hr (le_conjugateSpanBy _ _ (mem_zpowers x))
  have ha2 : IsPGroup 2 (f.subgroupMap A).ker := by
    rw [ha]
    exact pCore_isPGroup.comap_subtype
  have hb2 : IsPGroup 2 (f.subgroupMap B).ker := by
    rw [hb]
    exact pCore_isPGroup.comap_subtype
  let e := hg.symm.action_prime_local_equiv f (QuotientGroup.mk'_surjective _)
    hr.quotient_pCore_eq_bot hb2 ha2 R (fun _ hr => mem_sup_right hr)
  have hf : IsMulCommutative (R.map f) := isMulCommutative_iff.mpr fun a b => e.injective (by
    rw [map_mul,map_mul,mul_comm])
  let : Group.IsSolvable J := (Group.isSolvable_iff_subgroup_quotient (pPrimeCore 3 J)).mpr
    ⟨hg.primeToThreeCore_solvable,hsol⟩
  exact point_solvable_action_sylow_not_abelian d hH hB hZ hs hz horiginal hPv hinter
    hg hne hrank x hx hr hff (Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)) hf

open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

/-- The literal O₃′ quotient of the original paired-point join cannot be
one of the two solvable models in F.6.18(2). -/
theorem point_not_solvable_F6_row
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
    ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) →
    P₁.pCoreIn 2 ≠ P₂.pCoreIn 2 →
    primeRank 3 J ≤ 2 →
    ∀ (x : J), (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
      letI := hr.normal
      letI := hr.elementary
      let W := conjugateSpanBy (zpowers x) ⊤
      IsFFModule (ChapterB.InternalThompsonAction.action W) →
      ¬ (Nonempty ((J ⧸ pPrimeCore 3 J) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
        ∃ N : Subgroup (J ⧸ pPrimeCore 3 J), ∃ _ : N.Normal,
          IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
          Nonempty (((J ⧸ pPrimeCore 3 J) ⧸ N) ≃* FSource.E4)) := by
  intro P₂ J hg hne hrank x hx hr
  let := hr.normal
  let := hr.elementary
  intro W hff hmodel
  let q := QuotientGroup.mk' (pPrimeCore 3 J)
  have hBJ : ChapterB.baumann (T : Subgroup G) ≤ J := le_sup_right.trans le_sup_right
  have hJv : J ≤ Gv (markedV d.flag.flag.module) := sup_le hPv (sup_le
    ((map_subtype_le _).trans inf_le_right)
    ((source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz _
      d.flag.flag.vector_mem d.flag.flag.vector_not_mem).le.trans inf_le_right))
  obtain ⟨S,hS⟩ := (point_baumann_sylow d hH hB hZ hs hz).restrict hBJ hJv
  have hSR : (S : Subgroup J) = (ChapterB.baumann (T : Subgroup G)).subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le hBJ]
  obtain ⟨hsol,hcomm⟩ := FSource.solvable_row_sylow_abelian
    (S.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 3 J))) hmodel
  have hcomm' : IsMulCommutative
      (((ChapterB.baumann (T : Subgroup G)).subgroupOf J).map q) := by
    change IsMulCommutative ((S : Subgroup J).map q) at hcomm
    rwa [hSR] at hcomm
  exact point_solvable_quotient_sylow_not_abelian d hH hB hZ hs hz horiginal hPv
    hinter hg hne hrank x hx hr hff hsol hcomm'

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
