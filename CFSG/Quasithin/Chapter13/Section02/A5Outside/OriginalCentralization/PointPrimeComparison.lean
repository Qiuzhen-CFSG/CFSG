module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointGeneration
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SourceB5.Complete
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.Applicability

/-!
# The actual map from the F.6 quotient to the point-span action

The point-action two-residual lies in its normal offender subgroup. Complete
corrected B.5 eliminates the prime-to-three core of that subgroup; its
two-group quotient and the reduced action eliminate the ambient prime-to-three
core as well. Consequently O₃′ of the original point join lies in the span
centralizer, and the original projection factors through a surjection from
the F.6 quotient to the faithful span action.

The kernel is the actual image of the span centralizer and is solvable.
The map commutes with both original quotient projections on every element.
SourceAssembly/PointPrimeComparison supplies these facts after each Sylow
rechoice. This does not identify the two quotient groups or finish their
nonsolvable model comparison.

Source: Aschbacher--Smith 13.2.12, printed p.882; B.5.3--6 and F.6.8--18.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section06.CentralizerReduction Section06.CentralizerReduction.A5Module
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The actual faithful point-span action has trivial prime-to-three core. -/
theorem point_action_threePrimeCore_eq_bot
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
    IsSQTK KnownSimple.IsKnownSimple J →
    ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) →
    ∀ (x : J), (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
      letI := hr.normal
      letI := hr.elementary
      let W := conjugateSpanBy (zpowers x) ⊤
      IsFFModule (ChapterB.InternalThompsonAction.action W) →
        pPrimeCore 3 (J ⧸ centralizer (W : Set J)) = ⊥ := by
  intro P₂ J hSQ hg x hx hr
  let := hr.normal
  let := hr.elementary
  intro W hff
  let f := QuotientGroup.mk' (centralizer (W : Set J))
  let ρ := ChapterB.InternalThompsonAction.action W
  let N := offenderSubgroup ρ
  let : N.Normal := offenderSubgroup_normal ρ
  let σ := ρ.comp N.subtype
  have hf : Function.Injective ρ := NormalElementaryQuotient.representation_injective W f
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hh := offender_source_hypothesis hSQ f (QuotientGroup.mk'_surjective _)
    hr.quotient_pCore_eq_bot ρ hf
  obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
  have hffN : IsFFModule σ :=
    ⟨A.subgroupOf N,(hA.isOffender ρ).subgroupOf ρ (hA.le_offenderSubgroup ρ)⟩
  have hN : pPrimeCore 3 N = ⊥ :=
    FFAlternatives.SourceB5.classification.threePrimeCore_eq_bot σ hh hffN
  have hq := (point_action_residual_le_offender d hH hB hZ hs hz
    horiginal hBP hPv hinter hg x hx hr).2
  exact pPrimeCore_eq_bot_of_pCore_eq_bot_of_quotient N hN hq hr.quotient_pCore_eq_bot

/-- The original F.6 quotient surjects onto the actual span action through
its literal projection; its kernel is solvable. No quotient isomorphism is assumed. -/
theorem point_action_prime_comparison
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
    IsSQTK KnownSimple.IsKnownSimple J →
    ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) →
    ∀ (x : J), (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
      letI := hr.normal
      letI := hr.elementary
      let W := conjugateSpanBy (zpowers x) ⊤
      let f := QuotientGroup.mk' (centralizer (W : Set J))
      let q := QuotientGroup.mk' (pPrimeCore 3 J)
      IsFFModule (ChapterB.InternalThompsonAction.action W) →
      pPrimeCore 3 (J ⧸ centralizer (W : Set J)) = ⊥ ∧
      pPrimeCore 3 J ≤ centralizer (W : Set J) ∧
      ∃ g : (J ⧸ pPrimeCore 3 J) →* (J ⧸ centralizer (W : Set J)),
        Function.Surjective g ∧ (∀ j : J, g (q j) = f j) ∧
        g.ker = (centralizer (W : Set J)).map q ∧ Group.IsSolvable g.ker := by
  intro P₂ J hSQ hg x hx hr
  let := hr.normal
  let := hr.elementary
  intro W f q hff
  have hD := point_action_threePrimeCore_eq_bot d hH hB hZ hs hz horiginal hBP hPv
    hinter hSQ hg x hx hr hff
  have hle : pPrimeCore 3 J ≤ centralizer (W : Set J) := by
    have hh : (pPrimeCore 3 J).map f ≤ pPrimeCore 3 (J ⧸ centralizer (W : Set J)) :=
      le_sSup ⟨Normal.map inferInstance f (QuotientGroup.mk'_surjective _),
        pPrimeCore_coprime_card.of_dvd_right (card_map_dvd _ _)⟩
    rw [hD] at hh
    have hk := (Subgroup.map_eq_bot_iff _).mp (bot_unique hh)
    rwa [QuotientGroup.ker_mk'] at hk
  let g := QuotientGroup.lift (pPrimeCore 3 J) f
    (by simpa only [f,QuotientGroup.ker_mk'] using hle)
  have hgf (j : J) : g (q j) = f j := rfl
  have hgSurj : Function.Surjective g := by
    intro y
    obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (W : Set J)) y
    exact ⟨q j,hgf j⟩
  have hk : g.ker = (centralizer (W : Set J)).map q := by
    ext y
    obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 3 J) y
    constructor
    · intro hy
      have hj : j ∈ centralizer (W : Set J) := (QuotientGroup.eq_one_iff _).mp hy
      exact mem_map_of_mem q hj
    · rintro ⟨c,hc,he⟩
      rw [←he]
      exact (QuotientGroup.eq_one_iff c).mpr hc
  have hsol := (point_span_action_comparison d hH hB hZ hs hz horiginal hPv hinter
    hg x hx W hr (le_conjugateSpanBy _ _ (mem_zpowers x))).1
  let := hsol
  have hgsol : Group.IsSolvable g.ker := by
    rw [hk]
    exact Group.isSolvable_of_surjective (q.subgroupMap_surjective (centralizer (W : Set J)))
  exact ⟨hD,hle,g,hgSurj,hgf,hk,hgsol⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
