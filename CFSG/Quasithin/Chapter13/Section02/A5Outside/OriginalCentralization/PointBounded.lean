module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointOffender
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SylowBound
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.Targets
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SourceB5.Quasisimple

/-!
# Bounded B.5 actors on the original point span

F.6.18 bounds the Sylow two-subgroups of the O₃′ quotient by 128. The
original local comparison restricts to the common Baumann Sylow subgroup,
so its two images have equal order. Sylow conjugacy transfers the bound to
every Sylow subgroup of the distinct faithful point-span quotient.

Apply the existing finite-parameter B.5 reduction to the actual normal
offender subgroup. The quasisimple alternative retains all six corrected
module clauses and gains actual bounded component and actor models; the
other three alternatives are unchanged. The universal SourceAssembly
application supplies F.6 from the original point join after each rechoice.

Source: Aschbacher--Smith 13.2.12, printed p.882; B.5.1 and F.6.18.
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

/-- The literal common Sylow isomorphism transports the complete F.6 bound. -/
theorem point_action_sylow_card_le
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
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) →
    (∃ R : Sylow 2 (J ⧸ pPrimeCore 3 J),
      FSource.SourceAlternative ((P₁.subgroupOf J).map q) ((P₂.subgroupOf J).map q) R ∨
      FSource.SourceAlternative ((P₂.subgroupOf J).map q) ((P₁.subgroupOf J).map q) R) →
    ∀ (x : J), (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
      letI := hr.normal
      let W := conjugateSpanBy (zpowers x) ⊤
      ∀ R : Sylow 2 (J ⧸ centralizer (W : Set J)), Nat.card R ≤ 128 := by
  intro P₂ J q hg hrows x hx hr
  let := hr.normal
  intro W R
  let f := QuotientGroup.mk' (centralizer (W : Set J))
  let A := P₁.subgroupOf J
  let B := P₂.subgroupOf J
  let C := (ChapterB.baumann (T : Subgroup G)).subgroupOf J
  obtain ⟨_,ha,hb,_⟩ := point_span_action_comparison d hH hB hZ hs hz horiginal
    hPv hinter hg x hx W hr (le_conjugateSpanBy _ _ (mem_zpowers x))
  have ha2 : IsPGroup 2 (f.subgroupMap A).ker := by
    rw [ha]
    exact pCore_isPGroup.comap_subtype
  have hb2 : IsPGroup 2 (f.subgroupMap B).ker := by
    rw [hb]
    exact pCore_isPGroup.comap_subtype
  let e := hg.symm.action_prime_local_equiv f (QuotientGroup.mk'_surjective _)
    hr.quotient_pCore_eq_bot hb2 ha2 C (fun _ hc => mem_sup_right hc)
  have hBJ : ChapterB.baumann (T : Subgroup G) ≤ J := le_sup_right.trans le_sup_right
  have hJv : J ≤ Gv (markedV d.flag.flag.module) := sup_le hPv (sup_le
    ((map_subtype_le _).trans inf_le_right)
    ((source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz _
      d.flag.flag.vector_mem d.flag.flag.vector_not_mem).le.trans inf_le_right))
  obtain ⟨S,hS⟩ := (point_baumann_sylow d hH hB hZ hs hz).restrict hBJ hJv
  have hSC : (S : Subgroup J) = C := by
    apply map_injective J.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le hBJ]
  have he : Nat.card (S.mapSurjective (QuotientGroup.mk'_surjective (centralizer (W : Set J)))) =
      Nat.card (S.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 3 J))) := by
    change Nat.card ((S : Subgroup J).map f) = Nat.card ((S : Subgroup J).map q)
    rw [hSC]
    exact Nat.card_congr e.toEquiv
  obtain ⟨R₀,hR₀⟩ := hrows
  calc
    Nat.card R = Nat.card (S.mapSurjective (QuotientGroup.mk'_surjective _)) :=
      Nat.card_congr (R.equiv _).toEquiv
    _ = Nat.card (S.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 3 J))) := he
    _ = Nat.card R₀ := Nat.card_congr (Sylow.equiv _ R₀).toEquiv
    _ ≤ 128 := hR₀.elim FSource.source_alternative_sylow_card_le
      FSource.source_alternative_sylow_card_le

/-- The actual offender action has bounded quasisimple models or one of the
three remaining corrected B.5 alternatives. -/
theorem point_offender_bounded_source_alternatives
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
    IsSQTK KnownSimple.IsKnownSimple J →
    ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) →
    P₁.pCoreIn 2 ≠ P₂.pCoreIn 2 →
    (∃ R : Sylow 2 (J ⧸ pPrimeCore 3 J),
      let q := QuotientGroup.mk' (pPrimeCore 3 J)
      FSource.SourceAlternative ((P₁.subgroupOf J).map q) ((P₂.subgroupOf J).map q) R ∨
      FSource.SourceAlternative ((P₂.subgroupOf J).map q) ((P₁.subgroupOf J).map q) R) →
    ∀ (x : J), (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
      letI := hr.normal
      letI := hr.elementary
      let W := conjugateSpanBy (zpowers x) ⊤
      IsFFModule (ChapterB.InternalThompsonAction.action W) →
      let ρ := ChapterB.InternalThompsonAction.action W
      let N := offenderSubgroup ρ
      let σ := ρ.comp N.subtype
      Nonempty (QuasisimpleComparison.BoundedBranch σ) ∨
      Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase σ) ∨
      Nonempty (ChapterB.OuterSixThreeShape N) ∨
      Nonempty (ChapterB.SourceInduction.HyperplaneCase σ) := by
  intro P₂ J hSQ hg hne hrows x hx hr
  let := hr.normal
  let := hr.elementary
  intro W hff ρ N σ
  have hsmall := point_action_sylow_card_le d hH hB hZ hs hz horiginal hPv hinter
    hg hrows x hx hr
  rcases point_offender_source_alternatives d hH hB hZ hs hz horiginal hPv hinter
    hSQ hg hne x hx hr hff with ⟨hq,⟨c⟩⟩ | h
  · let c' := FFAlternatives.SourceB5.quasisimpleConclusion c
    obtain ⟨hm,ha⟩ := QuasisimpleComparison.projectiveLine_bounded_actor hsmall
      N.subtype N.subtype_injective σ hq c'
    exact Or.inl ⟨⟨hq,c',hm,ha⟩⟩
  · exact Or.inr h

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
