module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.Prepared
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SylowBound
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts
/-!
# The actual quotient construction with the corrected FF source contract

This separately named adapter reruns the established kernel argument using
the source-facing projective-line convention. It supplies the same genuine
Goldschmidt triple, both core equalities, faithful ambient action, offender
subgroup, two-group quotient, and literal Sylow fixed-space equality as
`ClassifiedAction`. Only the full FF source conclusion has changed.

The three-prime-core proof is independent of the triple-six offender clause,
so the elementary F.6.11 bridge and all geometric hypotheses are unchanged.
This prevents final assembly from needing the stronger legacy universal input.
The universal F.6.18 and corrected B.5.1/B.5.6 implications remain explicit.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 15.4.18,
p.1163; F.6.11/F.6.18, pp.306–310; B.5.1/B.5.6, pp.99–110; K.1.3, p.453.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.ProjectiveLine
attribute [local instance] offenderSubgroup_normal
universe u v

/-- Both complete source lists on the same actual action quotient. This is
input to the remaining comparison, not the resulting small-actor list. -/
structure ClassifiedAction {D : Type u} [Group D] [Finite D]
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
  ffAlternatives : FFAlternatives.ProjectiveLine.SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype)
  quotient_twoGroup : IsPGroup 2 (D ⧸ offenderSubgroup ρ)
  sylow_fixedSpace : ∃ S : Sylow 2 D,
    subspaceKernel ρ (fixedSpace ρ (S : Subgroup D)) ⊤ = (S : Subgroup D)

variable {H : Type u} [Group H] [Finite H]

private theorem quotient_lists_transport (G₁ G₂ A B : Subgroup H)
    [A.Normal] [B.Normal] (h : A = B)
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

/-- Apply the full F.6.18 input, discharging F.6.11 from its proved elementary source. -/
theorem apply_F618_of_goldschmidt {K : GroupClass.{u}}
    (source618 : F618Universal K) (hH : IsSQTK K H)
    (G₁ G₂ : Subgroup H) (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (different : (pCore 2 G₁).map G₁.subtype ≠ (pCore 2 G₂).map G₂.subtype) :
    F611Preserved G₁ G₂ ∧
      GoldschmidtAlternatives.Remaining (threePrimeImage G₁) (threePrimeImage G₂) :=
  apply_F618_of_different_cores f611Universal_of_elementary source618 hH G₁ G₂ triple different

/-- The actual offender's three-prime-core elimination closes the kernel bridge.
No identification of the offender group with the whole quotient is used. -/
theorem threePrimeCore_eq_twoCore_of_classifications {K : GroupClass.{u}}
    (sourceB : FFAlternatives.ProjectiveLine.CompleteClassificationInput.{u,u} K)
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

/-- The unreduced exhaustive source lists, now on the actual representation
quotient and its actual offender subgroup. All module extensions are retained. -/
theorem classifiedAction_of_goldschmidt {K : GroupClass.{u}}
    (source618 : F618Universal K)
    (sourceB : FFAlternatives.ProjectiveLine.CompleteClassificationInput.{u,u} K)
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
      ClassifiedAction K (quotientAction P Z hC)
        (G₁.map coreProjection) (G₂.map coreProjection) := by
  have hk := threePrimeCore_eq_twoCore_of_classifications sourceB hH G₁ G₂ triple
    P Z Y₁ Y₂ hC hF hgen h₁ h₂ hZY hJ
  obtain ⟨hp, hf⟩ := apply_F618_of_goldschmidt source618 hH G₁ G₂ triple different
  obtain ⟨hb, hw⟩ := offenderFFHypothesis_and_witness P Z hC hH Y₁ hF h₁ hZY
  obtain ⟨ht, hf'⟩ := quotient_lists_transport G₁ G₂ _ _ hk hp.triple hf
  refine ⟨hk, hp, ?_⟩
  refine ⟨quotientAction_injective P Z hC, coreQuotient_twoCore,
    threePrimeCore_eq_twoCore_iff.mp hk, ht, hf', hb, hw, sourceB.general _ _ _ hb,
    quotient_offenderGroup_isTwoGroup P Z hC Y₁ Y₂ hgen h₁ h₂ hJ, ?_⟩
  · exact ⟨P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)),
      quotientAction_sylow_fixedSpace_kernel P Z hC⟩


/-- Reuse a legacy consumer on a branch whose full action conclusion is
unchanged. For B.5.6(2)–(5) the supplied alternative is constructed directly
from the identical case record; no legacy universal implication is needed. -/
theorem ClassifiedAction.withLegacyAlternative {D : Type u} [Group D] [Finite D]
    {K : GroupClass.{u}} {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
    (h : ClassifiedAction K ρ G₁ G₂)
    (alternative : FFAlternatives.SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype)) :
    CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.ClassifiedAction K ρ G₁ G₂ :=
  ⟨h.faithful, h.twoCore, h.threePrimeCore, h.triple, h.goldschmidt,
    h.ffHypothesis, h.ffWitness, alternative, h.quotient_twoGroup, h.sylow_fixedSpace⟩

/-- The uniform bound is on every actual ambient Sylow subgroup. -/
theorem ClassifiedAction.sylow_card_le {D : Type u} [Group D] [Finite D]
    {K : GroupClass.{u}} {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
    (h : ClassifiedAction K ρ G₁ G₂) (S : Sylow 2 D) : Nat.card S ≤ 128 := by
  obtain ⟨T, hT⟩ := h.triple.intersection_sylow
  rw [Nat.card_congr (S.equiv T).toEquiv,
    ← Nat.card_congr (MulEquiv.subgroupCongr hT).toEquiv]
  exact h.goldschmidt.intersection_card_le
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.ProjectiveLine
