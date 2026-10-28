module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointKernel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.ComplementSpan
public import CFSG.Quasithin.ChapterF.Section06.Elementary.FourModule
public import Theory.Representation.NormalElementaryQuotient.NormalMoved

/-!
# The original complementary point has no normal four-element support

The actual local orbit under O²(C_L(v)) spans a four-group and contains the
complementary point in its commutator. In the full point join, a normal
four-group containing this point would force equality of the two point
cores by F.6.7, contrary to their established inequality. The elementary
full orbit span therefore has more than four elements.

If the second residual has normal image in the faithful quotient by the
centralizer of that span, the commutator is normal and contains the seed.
It consequently equals the whole span. Literal commutator coordinates give
the same strict cardinal bound on its moved subspace. This is the obstruction
to the normal natural-plane conclusion in the solvable FF comparison; the
classification comparison itself remains a separate source obligation.

Source: Aschbacher--Smith 13.2.12, printed p.882.
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

/-- The same moving complementary point cannot lie in a normal four-group
of the original point join: the already unequal point cores would coincide. -/
theorem point_no_normal_four
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
    ∀ E : Subgroup J, E.Normal → IsElementaryAbelian 2 E → Nat.card E = 4 → x ∈ E → False := by
  intro P₂ J hg hne x hx E hE hel hcard hxE
  let := hE
  let := hel
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour E := ⟨hcard,IsElementaryAbelian.exponent_eq_prime⟩
  let A := P₁.subgroupOf J
  let B := P₂.subgroupOf J
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
  have he := congrArg (map J.subtype) (hg.cores_eq_of_normal_four E x hxE hcx hnA hnB)
  change ((P₁.subgroupOf J).pCoreIn 2).map J.subtype =
    ((P₂.subgroupOf J).pCoreIn 2).map J.subtype at he
  rw [pCoreIn_subgroupOf 2 P₁ J le_sup_left,pCoreIn_subgroupOf 2 P₂ J le_sup_right,
    map_subgroupOf_eq_of_le ((pCoreIn_le 2 P₁).trans le_sup_left),
    map_subgroupOf_eq_of_le ((pCoreIn_le 2 P₂).trans le_sup_right)] at he
  exact hne he

private theorem local_span_le_global_span
    {J : Subgroup G} (hKJ : Lv L (markedV d.flag.flag.module) ≤ J)
    (x : J) (hx : (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module) :
    complementSpan d.flag.flag.module ≤ (conjugateSpanBy (zpowers x) ⊤).map J.subtype := by
  rw [map_conjugateSpanBy,MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype]
  change complementSpan d.flag.flag.module ≤ conjugateSpanBy (zpowers (x:G)) J
  rw [hx]
  exact conjugateSpanBy_mono le_rfl hKJ

/-- The full complementary-point span is strictly larger than the actual
local four-group. This uses the unequal original point cores, not a model tag. -/
theorem point_span_card_gt_four
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
    IsElementaryAbelian 2 (conjugateSpanBy (zpowers x) ⊤) →
      4 < Nat.card (conjugateSpanBy (zpowers x) ⊤) := by
  intro P₂ J hg hne x hx hel
  let W := conjugateSpanBy (zpowers x) ⊤
  have hle := card_le_of_le (local_span_le_global_span d
    (show Lv L (markedV d.flag.flag.module) ≤ J from le_sup_left.trans le_sup_right) x hx)
  rw [complementSpan_card,card_map_of_injective J.subtype_injective] at hle
  change 4 ≤ Nat.card W at hle
  have hn : W.Normal := normalizer_eq_top_iff.mp
    (top_unique (le_normalizer_conjugateSpanBy (zpowers x) ⊤))
  have hneq : Nat.card W ≠ 4 := fun he => point_no_normal_four d hH hB hZ hs hz
    horiginal hPv hinter hg hne x hx W hn hel he (le_conjugateSpanBy _ _ (mem_zpowers x))
  change 4 < Nat.card W
  omega

/-- In the literal faithful action, a normal second-residual image moves the
whole span. Its moved module therefore has more than four elements. -/
theorem point_moved_support_gt_four_of_normal_image
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
      (K.map f).Normal →
        ⁅W,K⁆ = W ∧
        4 < Nat.card (subspaceCommutator (ChapterB.InternalThompsonAction.action W) ⊤ (K.map f)) := by
  intro P₂ J hg hne x hx hr
  let := hr.normal
  let := hr.elementary
  intro W K f hKn
  let := hKn
  have hKJ : Lv L (markedV d.flag.flag.module) ≤ J := le_sup_left.trans le_sup_right
  have hcm : (⁅W,K⁆ : Subgroup J).map J.subtype =
      ⁅W.map J.subtype,Lv L (markedV d.flag.flag.module)⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le hKJ]
  have hxcomm : x ∈ ⁅W,K⁆ := by
    have hh := commutator_mono (local_span_le_global_span d hKJ x hx)
      (le_refl (Lv L (markedV d.flag.flag.module)))
    have hm := hh (complement_mem_commutator_span d.flag.flag.module)
    rw [←hx,←hcm] at hm
    obtain ⟨y,hy,he⟩ := hm
    exact (J.subtype_injective he) ▸ hy
  have hn : (⁅W,K⁆ : Subgroup J).Normal :=
    NormalElementaryQuotient.commutator_normal_of_image_normal W f
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K
  let := hn
  have he : ⁅W,K⁆ = W := le_antisymm (commutator_le_left W K)
    (conjugateSpanBy_le (zpowers_le.mpr hxcomm) le_normalizer_of_normal)
  let : IsElementaryAbelian 2 (⁅W,K⁆ : Subgroup J) :=
    IsElementaryAbelian.of_injective (inclusion (commutator_le_left W K)) (inclusion_injective _)
  refine ⟨he,?_⟩
  have hc := Nat.card_congr (NormalElementaryQuotient.movedEquiv W f
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K).toEquiv
  change Nat.card (⁅W,K⁆ : Subgroup J) =
    Nat.card (subspaceCommutator (ChapterB.InternalThompsonAction.action W) ⊤ (K.map f)) at hc
  rw [←hc,he]
  exact point_span_card_gt_four d hH hB hZ hs hz horiginal hPv hinter hg hne x hx hr.elementary

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
