module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointPrimeComparison
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointHyperplane
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleSolvableImage
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.PrimeProduct.FFSpectrum
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ProductComparison.Obstruction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.OuterGroupComparison

/-!
# Quasisimple comparison on the original point-span action

In the F.6 product row, the simple perfect PSL₂ factor injects through the
actual solvable kernel. Its defining prime divides the offender group because
the remaining quotient is a two-group. The Sylow bound and the full corrected
B.5 alternatives instead bound that prime by seven, a contradiction.

Every surviving corrected F.6 row has quasisimple F*. The actual quotient
map transfers this to the faithful point action. The two-factor and outer
B.5 branches then contradict ambient quasisimplicity. Together with the
already proved S₃ and hyperplane exclusions, this leaves the bounded
quasisimple conclusion with all six corrected module clauses.

The original SQTK cover, both quotient maps, and both local vertices are
used literally. SourceAssembly/PointQuasisimple applies this after each
original rechoice. The remaining model and module exclusions are separate.
Source: Aschbacher--Smith 13.2.12, printed p.882; B.5.1--6 and F.6.18.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section06.CentralizerReduction Section06.CentralizerReduction.A5Module
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open Chapter15.Section03.TerminalRecognition.Intersection
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

private theorem no_prime_product_solvable_image
    {D E : Type*} [Group D] [Group E] [Finite D] [Finite E]
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) E M)
    (g : D →* E) (hg : Function.Surjective g) [Group.IsSolvable g.ker]
    (hclass : FFAlternatives.ProjectiveLine.AdequateSourceAlternative
      (ρ.comp (offenderSubgroup ρ).subtype))
    (hq : letI := offenderSubgroup_normal ρ; IsPGroup 2 (E ⧸ offenderSubgroup ρ))
    {S : Sylow 2 D} (r : FSource.ProductRow S)
    (hs : Nonempty (S ≃* DihedralGroup 4)) : False := by
  let N := offenderSubgroup ρ
  let : N.Normal := offenderSubgroup_normal ρ
  let σ := ρ.comp N.subtype
  have hgen : offenderSubgroup σ = ⊤ := offenderSubgroup_restrict_eq_top ρ
  have h8 : Nat.card S = 8 := by
    rw [Nat.card_congr hs.some.toEquiv,DihedralGroup.nat_card]
  have h16 : ¬ 16 ∣ Nat.card N := by
    intro hd
    have hh : 2 ^ 4 ∣ Nat.card D := hd.trans
      (N.card_subgroup_dvd_card.trans (card_dvd_of_surjective g hg))
    have hd' := S.pow_dvd_card_of_pow_dvd_card hh
    rw [h8] at hd'
    norm_num at hd'
  let : IsSimpleGroup r.first := LowRows.PrimeProduct.first_simple r
  let : Group.IsPerfect r.first := LowRows.PrimeProduct.first_perfect r
  have hinj : Function.Injective (g.comp r.first.subtype) := by
    rw [←MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (g.comp r.first.subtype).ker inferInstance with h | h
    · exact h
    · have hle : r.first ≤ g.ker := by
        intro a ha
        exact h.ge (mem_top (⟨a,ha⟩ : r.first))
      have hsol : Group.IsSolvable r.first := Group.isSolvable_of_isSolvable_injective
        (f := inclusion hle) (inclusion_injective hle)
      exact (Group.IsPerfect.not_isSolvable r.first hsol).elim
  have hd : r.field.prime ∣ Nat.card E :=
    (LowRows.PrimeProduct.prime_dvd_first_card r).trans
      (card_dvd_of_injective (g.comp r.first.subtype) hinj)
  have ho : Odd r.field.prime := Nat.odd_iff.mpr (by have := r.congruence; omega)
  have hn : r.field.prime ∣ Nat.card N := by
    obtain ⟨k,hk⟩ := hq.exists_card_eq
    have he : Nat.card E = Nat.card N * 2 ^ k := by
      rw [←hk,←Subgroup.index_eq_card,Subgroup.card_mul_index]
    rw [he] at hd
    exact ((Nat.coprime_two_right.mpr ho).pow_right k).dvd_of_dvd_mul_right hd
  have hle : r.field.prime ≤ 7 := by
    cases hclass with
    | outerSixThree c =>
      exact LowRows.PrimeProduct.FFSpectrum.outerShape_prime_le_seven
        σ hgen c r.field.prime_isPrime hn
    | trivial c =>
      exact LowRows.PrimeProduct.FFSpectrum.prime_le_seven_projectiveLine
        σ hgen h16 (.trivial c) _ r.field.prime_isPrime hn
    | quasisimple hq c =>
      exact LowRows.PrimeProduct.FFSpectrum.prime_le_seven_projectiveLine
        σ hgen h16 (.quasisimple hq c) _ r.field.prime_isPrime hn
    | symmetricThree c =>
      exact LowRows.PrimeProduct.FFSpectrum.prime_le_seven_projectiveLine
        σ hgen h16 (.symmetricThree c) _ r.field.prime_isPrime hn
    | twoFactors c =>
      exact LowRows.PrimeProduct.FFSpectrum.prime_le_seven_projectiveLine
        σ hgen h16 (.twoFactors c) _ r.field.prime_isPrime hn
    | hyperplane c =>
      exact LowRows.PrimeProduct.FFSpectrum.prime_le_seven_projectiveLine
        σ hgen h16 (.hyperplane c) _ r.field.prime_isPrime hn
  have := LowRows.PrimeProduct.prime_lower r
  omega

private theorem quasisimple_of_source_comparison
    {D E : Type*} [Group D] [Group E] [Finite D] [Finite E]
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) E M)
    (g : D →* E) (hg : Function.Surjective g) [Group.IsSolvable g.ker]
    (hclass : FFAlternatives.ProjectiveLine.AdequateSourceAlternative
      (ρ.comp (offenderSubgroup ρ).subtype))
    (hq : letI := offenderSubgroup_normal ρ; IsPGroup 2 (E ⧸ offenderSubgroup ρ))
    (hnotrow : ¬ (Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ N : Subgroup D, ∃ _ : N.Normal,
        IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
        Nonempty ((D ⧸ N) ≃* FSource.E4)))
    {A B : Subgroup D} {S : Sylow 2 D} (hncyc : ¬ Nonempty (S ≃* FSource.C 2))
    (hrows : FSource.SourceAlternative A B S) :
    IsQuasisimple (generalizedFitting D) ∧ IsQuasisimple (generalizedFitting E) := by
  have hD : IsQuasisimple (generalizedFitting D) := by
    rcases hrows with (hr | r) | r
    · cases hr with
      | one hs _ _ _ => exact (hncyc hs).elim
      | two hm => exact (hnotrow hm).elim
      | three r hs _ _ => exact (no_prime_product_solvable_image ρ g hg hclass hq r hs).elim
      | four _ _ _ _ _ h _ _ _ => exact h
      | five _ _ _ _ _ h _ _ _ => exact h
      | six _ _ h _ _ _ => exact h
      | seven _ h _ _ _ => exact h
      | eight _ h _ _ _ => exact h
      | nine _ h _ _ _ => exact h
      | ten _ _ _ _ _ h _ _ _ => exact h
      | eleven _ h _ _ _ => exact h
      | twelve _ h _ _ _ => exact h
      | thirteen _ _ h _ _ _ => exact h
    · exact r.some.quasisimple
    · exact r.some.quasisimple
  let := hD
  exact ⟨hD,(quasisimple_generalizedFitting_image_of_solvable_kernel g hg).2⟩

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The original two quotients have quasisimple F*, and the full corrected
B.5 conclusion on the actual offender action is its bounded quasisimple branch. -/
theorem point_action_quasisimple_source
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
    P₁.pCoreIn 2 ≠ P₂.pCoreIn 2 →
    (∃ R : Sylow 2 (J ⧸ pPrimeCore 3 J),
      let q := QuotientGroup.mk' (pPrimeCore 3 J)
      ¬ Nonempty (R ≃* FSource.C 2) ∧
        (FSource.SourceAlternative ((P₁.subgroupOf J).map q) ((P₂.subgroupOf J).map q) R ∨
         FSource.SourceAlternative ((P₂.subgroupOf J).map q) ((P₁.subgroupOf J).map q) R)) →
    (¬ (Nonempty ((J ⧸ pPrimeCore 3 J) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ N : Subgroup (J ⧸ pPrimeCore 3 J), ∃ _ : N.Normal,
        IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
        Nonempty (((J ⧸ pPrimeCore 3 J) ⧸ N) ≃* FSource.E4))) →
    ∀ (x : J), (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
      letI := hr.normal
      letI := hr.elementary
      let W := conjugateSpanBy (zpowers x) ⊤
      IsFFModule (ChapterB.InternalThompsonAction.action W) →
      let ρ := ChapterB.InternalThompsonAction.action W
      IsQuasisimple (generalizedFitting (J ⧸ pPrimeCore 3 J)) ∧
      IsQuasisimple (generalizedFitting (J ⧸ centralizer (W : Set J))) ∧
      Nonempty (QuasisimpleComparison.BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype)) := by
  intro P₂ J hSQ hg hne hrows hnotrow x hx hr
  let := hr.normal
  let := hr.elementary
  intro W hff ρ
  let f := QuotientGroup.mk' (centralizer (W : Set J))
  have hf : Function.Injective ρ := NormalElementaryQuotient.representation_injective W f
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hh := offender_source_hypothesis hSQ f (QuotientGroup.mk'_surjective _)
    hr.quotient_pCore_eq_bot ρ hf
  have hclass := FFAlternatives.SourceB5.classification.general _ _ _ hh
  obtain ⟨_,_,g,hgSurj,_,_,hgsol⟩ := point_action_prime_comparison d hH hB hZ hs hz
    horiginal hBP hPv hinter hSQ hg x hx hr hff
  let := hgsol
  have hq := (point_action_residual_le_offender d hH hB hZ hs hz
    horiginal hBP hPv hinter hg x hx hr).2
  obtain ⟨R,hncyc,hrows'⟩ := hrows
  have hquasi := hrows'.elim
    (quasisimple_of_source_comparison ρ g hgSurj hclass hq hnotrow hncyc)
    (quasisimple_of_source_comparison ρ g hgSurj hclass hq hnotrow hncyc)
  refine ⟨hquasi.1,hquasi.2,?_⟩
  rcases point_offender_bounded_source_alternatives d hH hB hZ hs hz horiginal hPv
    hinter hSQ hg hne ⟨R,hrows'⟩ x hx hr hff with hb | ⟨c⟩ | ⟨c⟩ | hc
  · exact hb
  · obtain ⟨c⟩ := c
    exact (ProductComparison.sourceTwoFactor_not_quasisimple ρ
      (FFAlternatives.SourceB5.pair c) hquasi.2).elim
  · obtain ⟨c⟩ := c
    exact (OuterGroupComparison.outerShape_not_quasisimple ρ c hquasi.2).elim
  · have hBJ : ChapterB.baumann (T : Subgroup G) ≤ J := le_sup_right.trans le_sup_right
    have hJv : J ≤ Gv (markedV d.flag.flag.module) := sup_le hPv (sup_le
      ((map_subtype_le _).trans inf_le_right)
      ((source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz _
        d.flag.flag.vector_mem d.flag.flag.vector_not_mem).le.trans inf_le_right))
    exact (point_offender_not_hyperplane d hH hB hZ hs hz hBJ hJv x hx hr hc).elim

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
