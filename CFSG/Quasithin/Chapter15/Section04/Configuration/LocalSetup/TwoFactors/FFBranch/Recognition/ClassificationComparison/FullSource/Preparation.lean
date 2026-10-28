module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FullSource.Basic
/-!
# Prepare the original quotient using the full source inputs

The FF classifier on the actual offender proves O₃′(H) = O₂(H). The
elementary F.6.11 theorem preserves the Goldschmidt triple and prevents both
local two-cores from vanishing. Apply the complete source classification
on this same quotient, retaining the original action and Sylow data.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.6.18, pp.309–310; B.5.1/B.5.6, pp.99–110; 15.4.18, p.1163.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FullSource
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {H : Type u} [Group H] [Finite H]
omit [Finite H] in
private theorem transport_core_bots (G₁ G₂ A B : Subgroup H)
    [A.Normal] [B.Normal] (h : A = B)
    (h₁ : pCore 2 (G₁.map (QuotientGroup.mk' B)) = ⊥)
    (h₂ : pCore 2 (G₂.map (QuotientGroup.mk' B)) = ⊥) :
    pCore 2 (G₁.map (QuotientGroup.mk' A)) = ⊥ ∧
      pCore 2 (G₂.map (QuotientGroup.mk' A)) = ⊥ := by
  subst B
  exact ⟨h₁,h₂⟩

theorem classifiedAction_of_adequate_goldschmidt {K : GroupClass.{u}}
    (source618 : FSource.SourceClassificationInput K)
    (sourceB : FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u} K)
    (hH : IsSQTK K H) (G₁ G₂ : Subgroup H)
    (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (different : (pCore 2 G₁).map G₁.subtype ≠ (pCore 2 G₂).map G₂.subtype)
    (P : Sylow 2 H) (Z Y₁ Y₂ : Subgroup H)
    [IsElementaryAbelian 2 (moduleClosure Z)]
    (hC : centralizer (Z : Set H) = (P : Subgroup H))
    (hF : Theory.GroupTheory.generalizedFitting H = pCore 2 H)
    (hgen : Y₁ ⊔ Y₂ ⊔ (P : Subgroup H) = ⊤)
    (h₁ : Y₁ = ⁅Y₁, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (h₂ : Y₂ = ⁅Y₂, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (hZY : ⁅Z, Y₁⁆ ≠ ⊥)
    (hJ : (Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)).map coreProjection ≤
      offenderGroup P Z hC) :
    pPrimeCore 3 H = pCore 2 H ∧ F611Preserved G₁ G₂ ∧
      Nonempty (ClassifiedAction K (quotientAction P Z hC)
        (G₁.map coreProjection) (G₂.map coreProjection)) := by
  obtain ⟨S,hS⟩ := (f611Conclusion_of_goldschmidt triple).core_sylow
  obtain ⟨hb,hw⟩ := offenderFFHypothesis_and_witness P Z hC hH Y₁ hF h₁ hZY
  have ha := sourceB.general _ _ _ hb
  have hq := quotient_offenderGroup_isTwoGroup P Z hC Y₁ Y₂ hgen h₁ h₂ hJ
  have hk := threePrimeCore_eq_twoCore_of_offender_core P Z hC S hS hq
    (ha.threePrimeCore_eq_bot _ hb hw)
  obtain ⟨_,_,hp⟩ := apply_F611_of_different_cores f611Universal_of_elementary
    G₁ G₂ triple different
  have hn : pCore 2 (G₁.map coreProjection) ≠ ⊥ ∨
      pCore 2 (G₂.map coreProjection) ≠ ⊥ := by
    by_contra hh
    push Not at hh
    obtain ⟨h₁,h₂⟩ := transport_core_bots G₁ G₂ _ _ hk hh.1 hh.2
    exact different (original_local_cores_eq_of_trivial_images G₁ G₂ triple hp h₁ h₂)
  obtain ⟨Q,hQ,hsource⟩ := source618 (coreQuotient H) _ _
    (goldschmidt_twoCore_quotient G₁ G₂ triple)
    (threePrimeSQTKQuotient_of_core_eq hH hk)
  refine ⟨hk,hp,⟨{
    faithful := quotientAction_injective P Z hC
    twoCore := coreQuotient_twoCore
    threePrimeCore := threePrimeCore_eq_twoCore_iff.mp hk
    triple := goldschmidt_twoCore_quotient G₁ G₂ triple
    core_nontrivial := hn
    sylow := Q
    intersection := hQ
    goldschmidt := hsource
    ffHypothesis := hb
    ffWitness := hw
    ffAlternatives := ha
    quotient_twoGroup := hq
    sylow_fixedSpace := ?_ }⟩⟩
  exact ⟨P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)),
    quotientAction_sylow_fixedSpace_kernel P Z hC⟩
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FullSource
