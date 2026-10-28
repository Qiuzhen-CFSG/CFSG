module
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.TwoCoreRecognition
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.ComponentRecognition.FullSource
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.Quotient.FullSource

/-!
# The full source15.4.21--24 endgame with corrected F classification

In the two-core branch the literal FF quotient comparison uses every corrected
source row and the original adequate projective-line classifier. It gives the
actual S3-by-S3 quotient and normalizes both original residual factors. The
non-two-core branch applies the complete source15.4.22 component recognition.
Together they feed the original15.4.23 intersection contradiction.

No old restricted F618Universal or inferred local marks are used. Source:
Aschbacher--Smith,15.4.21--24, pp.1164--1165.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors
open FFBranch FFBranch.ClassificationComparison
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
namespace CFSG.Quasithin.Chapter15.Section04.SourceRecognition.TwoCore.FullSource
universe u

/-- A generic two-core branch for the literal Goldschmidt triple. Equal cores
are handled by solvable FF theory; unequal cores use existing recognition. -/
theorem normal_factors_of_goldschmidt
    {H : Type u} [Group H] [Finite H] {K : GroupClass.{u}}
    (sourceF : FSource.SourceClassificationInput K)
    (sourceB : FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u} K)
    (hH : IsSQTK K H) (A B : Subgroup H)
    (triple : ChapterF.IsGoldschmidtTriple A B)
    (P : Sylow 2 H) (Z Y₁ Y₂ : Subgroup H)
    [IsElementaryAbelian 2 (moduleClosure Z)]
    (hC : centralizer (Z : Set H) = (P : Subgroup H))
    (hF : generalizedFitting H = pCore 2 H)
    (hgen : Y₁ ⊔ Y₂ ⊔ (P : Subgroup H) = ⊤)
    (h₁ : Y₁ = ⁅Y₁, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (h₂ : Y₂ = ⁅Y₂, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (hZY : ⁅Z, Y₁⁆ ≠ ⊥)
    (hJ : (Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)).map coreProjection ≤
      offenderGroup P Z hC)
    (hp₁ : IsPPerfect 2 Y₁) (hp₂ : IsPPerfect 2 Y₂)
    (hn₁ : (P : Subgroup H) ≤ normalizer (Y₁ : Set H))
    (hn₂ : (P : Subgroup H) ≤ normalizer (Y₂ : Set H)) :
    Y₁.Normal ∧ Y₂.Normal := by
  have hc : ⁅Y₂, Y₁⁆ ≤ pCore 2 H := by
    by_cases heq : (pCore 2 A).map A.subtype = (pCore 2 B).map B.subtype
    · exact cross_le_core_of_solvable P Z Y₁ Y₂ hC hF h₁ h₂ hZY hJ
        (quotient_solvable_of_equal_cores A B triple heq)
    · obtain ⟨e⟩ := FFBranch.FullSource.symmetricThreeProduct_quotient_of_goldschmidt sourceF sourceB
        hH A B triple heq P Z Y₁ Y₂ hC hF hgen h₁ h₂ hZY hJ
      let := symmetricThreeProduct_derived_abelian
      let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
      have hk : q.ker = pCore 2 H := by
        ext x
        change e (QuotientGroup.mk' (pCore 2 H) x) = 1 ↔ x ∈ pCore 2 H
        rw [← e.map_one, e.injective.eq_iff]
        exact QuotientGroup.eq_one_iff x
      exact hk ▸ factor_commutator_le_kernel q Y₁ Y₂
        (Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)) h₁ h₂
  have hQ : pCore 2 H ≤ (P : Subgroup H) := pCore_isPGroup.le_sylow_of_normal P
  have h₂₁ := (normalizes_factor_of_commutator_le (pCore 2 H) Y₁ Y₂
    pCore_isPGroup hp₁ (hQ.trans hn₁) hc).2
  have h₁₂ := (normalizes_factor_of_commutator_le (pCore 2 H) Y₂ Y₁
    pCore_isPGroup hp₂ (hQ.trans hn₂) (by rw [commutator_comm]; exact hc)).2
  constructor
  · apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le (sup_le Y₁.le_normalizer h₂₁) hn₁
  · apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le (sup_le h₁₂ Y₂.le_normalizer) hn₂

open CFSG.Quasithin.Chapter15.Section04.Source

/-- The actual source pair, with generation and both normal factors.
The source identity for d.J is retained explicitly for its existing producer. -/
theorem source_lemma_15_4_21
    {G : Type u} [Group G] [Finite G] {d : Geometry G}
    (h : LocalData d) (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (sourceF : FSource.SourceClassificationInput.{u} CFSG.KnownSimple.IsKnownSimple)
    (sourceB : FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u}
      CFSG.KnownSimple.IsKnownSimple)
    (hJsource : d.J = ChapterB.thompsonJ (d.T : Subgroup G) 0)
    (i j : Bool) (hF : generalizedFitting (d.I i j) = pCore 2 (d.I i j)) :
    ((d.X i).subgroupOf (d.I i j)).Normal ∧
      ((d.Y j).subgroupOf (d.I i j)).Normal ∧
      d.I i j = (d.X i ⊔ d.Y j) ⊔ d.T₀ := by
  let I := d.I i j
  let P := h.sylow i j
  let Z := d.Z.subgroupOf I
  let U := (d.X i).subgroupOf I
  let W := (d.Y j).subgroupOf I
  have hZI : d.Z ≤ I := h.Z_le.trans (d.T₀_le_I i j)
  have hUI : d.X i ≤ I := d.X_le_I i j
  have hWI : d.Y j ≤ I := d.Y_le_I i j
  have hPT : (P : Subgroup I).map I.subtype ≤ (d.T : Subgroup G) := by
    rw [h.sylow_image]
    exact d.T₀_le_T
  have hP : (P : Subgroup I) = d.T₀.subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [h.sylow_image, map_subgroupOf_eq_of_le (d.T₀_le_I i j)]
  have hC : centralizer (Z : Set I) = (P : Subgroup I) :=
    centralizer_seed_subgroupOf I (d.T : Subgroup G) d.Z P d.T.isPGroup'
      hPT hZI h.centralizer_Z
  let : IsElementaryAbelian 2 d.Z := h.Z_elementary
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.subgroupOf hZI
  let := moduleClosure_elementary P Z hC hF
  have hJambient : d.J = Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup G) :=
    hJsource.trans (ChapterB.thompsonJ_zero _)
  have hJT : (Stellmacher.elementaryAbelianMaxJ (P : Subgroup I)).map I.subtype = d.J := by
    rw [hJambient]
    apply thompson_sylow_image I (d.T : Subgroup G) P hPT
    rw [h.sylow_image, ← hJambient]
    exact h.J_le
  have hU : U = ⁅U, Stellmacher.elementaryAbelianMaxJ (P : Subgroup I)⁆ :=
    factor_commutator_subgroupOf I (d.X i) d.J _ hUI hJT (h.X_commutator i).symm
  have hW : W = ⁅W, Stellmacher.elementaryAbelianMaxJ (P : Subgroup I)⁆ :=
    factor_commutator_subgroupOf I (d.Y j) d.J _ hWI hJT (h.Y_commutator j).symm
  have hZU : ⁅Z, U⁆ ≠ ⊥ := by
    apply seed_factor_commutator_ne_bot_subgroupOf I d.Z (d.X i) hZI hUI
    intro hb
    apply h.X_outside i
    have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb)
    rw [h.centralizer_Z] at hc
    exact hc.trans h.T_normalizes_Y
  have hJ : (Stellmacher.elementaryAbelianMaxJ (P : Subgroup I)).map coreProjection ≤
      offenderGroup P Z hC := by
    apply Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.thompson_image_le_offender
      (P : Subgroup I) (moduleClosure Z)
      ((moduleClosure_le_twoCore P Z hC hF).trans (pCore_isPGroup.le_sylow_of_normal P))
      coreProjection
      ((QuotientGroup.ker_mk' _).trans (moduleClosure_centralizer P Z hC).symm)
      (quotientAction P Z hC)
    exact quotientAction_apply P Z hC
  have hgen : U ⊔ W ⊔ (P : Subgroup I) = ⊤ := by
    rw [hP, ← subgroupOf_sup hUI hWI,
      ← subgroupOf_sup (sup_le hUI hWI) (d.T₀_le_I i j),
      ← d.I_eq_join i j, subgroupOf_self]
  have hpU : IsPPerfect 2 U := (h.X_perfect i).of_surjective
    (subgroupOfEquivOfLe hUI).symm.toMonoidHom (subgroupOfEquivOfLe hUI).symm.surjective
  have hpW : IsPPerfect 2 W := (h.Y_perfect j).of_surjective
    (subgroupOfEquivOfLe hWI).symm.toMonoidHom (subgroupOfEquivOfLe hWI).symm.surjective
  have hnU : (P : Subgroup I) ≤ normalizer (U : Set I) := by
    rw [← subgroupOf_normalizer_eq hUI, hP]
    exact subgroupOf_mono I (h.X_normalized i)
  have hnW : (P : Subgroup I) ≤ normalizer (W : Set I) := by
    rw [← subgroupOf_normalizer_eq hWI, hP]
    exact subgroupOf_mono I (h.Y_normalized j)
  obtain ⟨hUn, hWn⟩ := normal_factors_of_goldschmidt sourceF sourceB
    (h.I_sqtk hG i j) ((d.G₁ i).subgroupOf I) ((d.G₂ j).subgroupOf I)
    (Chapter15.Section04.SourceRecognition.Source.source_triple h i j)
    P Z U W hC hF hgen hU hW hZU hJ hpU hpW hnU hnW
  exact ⟨hUn, hWn, d.I_eq_join i j⟩

/-- Actual application to the source assembly: the original two-core premise
is now discharged, leaving only genuine earlier-source inputs. -/
theorem source_endgame
    {G : Type u} [Group G] [Finite G] {d : Geometry G}
    (h : LocalData d) (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (sourceF : FSource.SourceClassificationInput.{u} CFSG.KnownSimple.IsKnownSimple)
    (sourceB : FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u}
      CFSG.KnownSimple.IsKnownSimple)
    (source115 : Chapter15.Section04.SourceRecognition.Source.Earlier115 (G := G))
    (hJsource : d.J = ChapterB.thompsonJ (d.T : Subgroup G) 0) : False :=
  Chapter15.Section04.SourceRecognition.Source.FullSource.false_of_twoCore_branch
    h hG sourceF source115 (fun i j hF =>
      (source_lemma_15_4_21 h hG sourceF sourceB hJsource i j hF).1)

end CFSG.Quasithin.Chapter15.Section04.SourceRecognition.TwoCore.FullSource
