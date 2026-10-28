module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ElementarySource
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.GoldschmidtAlternatives
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives
/-!
# The source and action classifications on one actual quotient

The full F.6.11 theorem is supplied by `ElementarySource`. B.5.1/B.5.6
eliminate the three-prime core of the actual offender subgroup, so the proved
kernel bridge identifies O_{3'}(H) with O₂(H). Equality transport then places
all surviving F.6.18 rows on the literal representation quotient H/O₂(H).
The full FF module alternatives remain on its actual offender subgroup.

`ClassifiedAction` is the input to the remaining comparison, not a small-group
classification conclusion. It retains the faithful ambient action, both trivial
cores, both complete source lists, the nontrivial FF witness, the two-group
quotient by the offender subgroup, and the actual Sylow fixed-space condition.
The full universal F.6.18 and B.5.1/B.5.6 implications remain parameters.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, F.6.11 and F.6.18, pp.306–310; B.5.1/B.5.6,
pp.99–110; final paragraph of 15.4.18, p.1163.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
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
  ffAlternatives : FFAlternatives.SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype)
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
    (sourceB : FFAlternatives.CompleteClassificationInput.{u,u} K)
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
    (sourceB : FFAlternatives.CompleteClassificationInput.{u,u} K)
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

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
