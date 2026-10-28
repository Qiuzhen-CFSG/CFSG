module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Adequate

/-!
# Adequate actual-action comparison

This is the actual Chapter 15 consumer of the adequate B.5.6 interface.  It
keeps the faithful action, the two core and three-prime-core conclusions, the
literal Goldschmidt factors, the SQTK cover and the Sylow fixed-space map.
Only the FF alternatives field is changed from the old full record to
`AdequateSourceAlternative`; the outer case therefore retains its actual
subgroup product and outer conjugation data without assuming a fixed-space
splitting.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives
attribute [local instance] offenderSubgroup_normal
universe u v

/-- The actual-action record with the adequate source alternatives. -/
structure AdequateClassifiedAction {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (K : GroupClass.{u}) (ρ : Representation (ZMod 2) D V)
    (G₁ G₂ : Subgroup D) : Prop where
  faithful : Function.Injective ρ
  twoCore : pCore 2 D = ⊥
  threePrimeCore : pPrimeCore 3 D = ⊥
  triple : ChapterF.IsGoldschmidtTriple G₁ G₂
  goldschmidt : GoldschmidtAlternatives.Remaining G₁ G₂
  ffHypothesis : FFHypothesis K (ρ.comp (offenderSubgroup ρ).subtype)
  ffWitness : IsFFModule (ρ.comp (offenderSubgroup ρ).subtype)
  ffAlternatives : AdequateSourceAlternative (ρ.comp (offenderSubgroup ρ).subtype)
  quotient_twoGroup : IsPGroup 2 (D ⧸ offenderSubgroup ρ)
  sylow_fixedSpace : ∃ S : Sylow 2 D,
    subspaceKernel ρ (fixedSpace ρ (S : Subgroup D)) ⊤ = (S : Subgroup D)

/-- The old actual-action record maps to the adequate one by forgetting only
the outer representation fields. -/
theorem ClassifiedAction.toAdequate {K : GroupClass.{u}}
    {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
    (h : ClassifiedAction K ρ G₁ G₂) : AdequateClassifiedAction K ρ G₁ G₂ where
  faithful := h.faithful
  twoCore := h.twoCore
  threePrimeCore := h.threePrimeCore
  triple := h.triple
  goldschmidt := h.goldschmidt
  ffHypothesis := h.ffHypothesis
  ffWitness := h.ffWitness
  ffAlternatives := h.ffAlternatives.toAdequate
  quotient_twoGroup := h.quotient_twoGroup
  sylow_fixedSpace := h.sylow_fixedSpace

private theorem quotient_lists_transport_adequate {X : Type*} [Group X] [Finite X]
    (G₁ G₂ A B : Subgroup X) (h : A = B)
    [A.Normal] [B.Normal]
    (ht : ChapterF.IsGoldschmidtTriple (G₁.map (QuotientGroup.mk' A))
      (G₂.map (QuotientGroup.mk' A)))
    (hf : GoldschmidtAlternatives.Remaining (G₁.map (QuotientGroup.mk' A))
      (G₂.map (QuotientGroup.mk' A))) :
    ChapterF.IsGoldschmidtTriple (G₁.map (QuotientGroup.mk' B))
      (G₂.map (QuotientGroup.mk' B)) ∧
    GoldschmidtAlternatives.Remaining (G₁.map (QuotientGroup.mk' B))
      (G₂.map (QuotientGroup.mk' B)) := by
  subst B
  exact ⟨ht, hf⟩

/-- The three-prime-core bridge with the adequate source classifier. -/
theorem adequate_threePrimeCore_eq_twoCore_of_classifications
    {H : Type u} [Group H] [Finite H] {K : GroupClass.{u}}
    (sourceB : AdequateCompleteClassificationInput.{u,u} K)
    (hH : IsSQTK K H) (G₁ G₂ : Subgroup H)
    (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (P : Sylow 2 H) (Z Y₁ Y₂ : Subgroup H)
    [IsElementaryAbelian 2 (moduleClosure Z)]
    (hC : centralizer (Z : Set H) = (P : Subgroup H))
    (hF : Theory.GroupTheory.generalizedFitting H = pCore 2 H)
    (hgen : Y₁ ⊔ Y₂ ⊔ (P : Subgroup H) = ⊤)
    (h₁ : Y₁ = ⁅Y₁, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (h₂ : Y₂ = ⁅Y₂, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (hZY : ⁅Z, Y₁⁆ ≠ ⊥)
    (hJ : (Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)).map coreProjection ≤
      offenderGroup P Z hC) : pPrimeCore 3 H = pCore 2 H := by
  obtain ⟨S, hS⟩ := (f611Conclusion_of_goldschmidt triple).core_sylow
  obtain ⟨hb, hw⟩ := offenderFFHypothesis_and_witness P Z hC hH Y₁ hF h₁ hZY
  exact mixed_threePrimeCore_eq_twoCore P Z Y₁ Y₂ hC S hS hgen h₁ h₂ hJ
    (sourceB.threePrimeCore_eq_bot _ hb hw)

/-- Construct the actual adequate classified action from the same F.6.18 and
Goldschmidt inputs used by the original comparison. -/
theorem adequateClassifiedAction_of_goldschmidt
    {H : Type u} [Group H] [Finite H] {K : GroupClass.{u}}
    (source618 : F618Universal K)
    (sourceB : AdequateCompleteClassificationInput.{u,u} K)
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
    (hJ : (Stellmacher.elementaryAbelianMaxJ (P : Sylow 2 H)).map coreProjection ≤
      offenderGroup P Z hC) :
    pPrimeCore 3 H = pCore 2 H ∧ F611Preserved G₁ G₂ ∧
      AdequateClassifiedAction K (quotientAction P Z hC)
        (G₁.map coreProjection) (G₂.map coreProjection) := by
  have hk := adequate_threePrimeCore_eq_twoCore_of_classifications sourceB hH G₁ G₂
    triple P Z Y₁ Y₂ hC hF hgen h₁ h₂ hZY hJ
  obtain ⟨hp, hf⟩ := apply_F618_of_goldschmidt source618 hH G₁ G₂ triple different
  obtain ⟨hb, hw⟩ := offenderFFHypothesis_and_witness P Z hC hH Y₁ hF h₁ hZY
  obtain ⟨ht, hf'⟩ := quotient_lists_transport_adequate G₁ G₂ _ _ hk hp.triple hf
  refine ⟨hk, hp, ?_⟩
  refine ⟨quotientAction_injective P Z hC, coreQuotient_twoCore,
    threePrimeCore_eq_twoCore_iff.mp hk, ht, hf', hb, hw,
    sourceB.general _ _ _ hb,
    quotient_offenderGroup_isTwoGroup P Z hC Y₁ Y₂ hgen h₁ h₂ hJ, ?_⟩
  exact ⟨P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)),
    quotientAction_sylow_fixedSpace_kernel P Z hC⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
