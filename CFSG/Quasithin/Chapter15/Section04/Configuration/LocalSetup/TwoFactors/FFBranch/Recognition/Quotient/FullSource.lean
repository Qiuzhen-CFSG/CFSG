module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FullSource
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.Quotient

/-!
# The actual mixed quotient from corrected full source classifiers

These consumers keep the intrinsic and ambient mixed hypotheses unchanged
and replace the legacy Goldschmidt classification premise by the complete
source statement. The actual two-core quotient is identified with S₃ × S₃.
The source-action comparison supplies all module exclusions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.6.18, pp.309–310; 15.4.18, p.1163.
-/
public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.FullSource
open ClassificationComparison
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {H : Type u} [Group H] [Finite H]
/-- Recognize the original two-core quotient from the intrinsic mixed data.
The comparison proves the kernel equality before identifying the quotient. -/
theorem symmetricThreeProduct_quotient_of_goldschmidt {K : GroupClass.{u}}
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
    (h₁ : Y₁ = ⁅Y₁, elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (h₂ : Y₂ = ⁅Y₂, elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (hZY : ⁅Z, Y₁⁆ ≠ ⊥)
    (hJ : (elementaryAbelianMaxJ (P : Subgroup H)).map coreProjection ≤
      offenderGroup P Z hC) :
    Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  obtain ⟨_, _, _, h⟩ := ClassificationComparison.FullSource.exhaustive_comparison_of_goldschmidt source618 sourceB
    hH G₁ G₂ triple different P Z Y₁ Y₂ hC hF hgen h₁ h₂ hZY hJ
  exact h.resolve_right (quotientAction_not_comparedBranch P Z hC)

/-- The identification used in 15.4.18 on the actual ambient factors inside I.
Baumann containment transports both raw commutator identities into I. -/
theorem mixed_symmetricThreeProduct_quotient
    {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
    (source618 : FSource.SourceClassificationInput K)
    (sourceB : FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u} K)
    (T : Sylow 2 G) (I Y₁ Y₂ Z : Subgroup G) (P : Sylow 2 I)
    (G₁ G₂ : Subgroup I) (hI : IsSQTK K I)
    (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (different : (pCore 2 G₁).map G₁.subtype ≠ (pCore 2 G₂).map G₂.subtype)
    [IsElementaryAbelian 2 (moduleClosure (Z.subgroupOf I))]
    (hC : centralizer (Z.subgroupOf I : Set I) = (P : Subgroup I))
    (hB : ChapterB.baumann (T : Subgroup G) ≤ (P : Subgroup I).map I.subtype)
    (hZI : Z ≤ I) (h₁I : Y₁ ≤ I) (h₂I : Y₂ ≤ I)
    (hF : Theory.GroupTheory.generalizedFitting I = pCore 2 I)
    (hgen : Y₁ ⊔ Y₂ ⊔ (P : Subgroup I).map I.subtype = I)
    (h₁ : Y₁ = ⁅Y₁, elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (h₂ : Y₂ = ⁅Y₂, elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hZY : ⁅Z, Y₁⁆ ≠ ⊥)
    (hJ : (elementaryAbelianMaxJ (P : Subgroup I)).map coreProjection ≤
      offenderGroup P (Z.subgroupOf I) hC) :
    Nonempty ((I ⧸ pCore 2 I) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  obtain ⟨_, _, _, h⟩ := ClassificationComparison.FullSource.mixed_exhaustive_comparison source618 sourceB T I Y₁ Y₂ Z P
    G₁ G₂ hI triple different hC hB hZI h₁I h₂I hF hgen h₁ h₂ hZY hJ
  exact h.resolve_right (quotientAction_not_comparedBranch P (Z.subgroupOf I) hC)

/-- Start with the ambient elementary seed and its original centralizer.
Construct the internal centralizer and elementary conjugate-span module;
only the authorized Thompson-image containment remains to be supplied. -/
theorem mixed_symmetricThreeProduct_quotient_of_ambient_seed
    {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
    (source618 : FSource.SourceClassificationInput K)
    (sourceB : FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u} K)
    (T : Sylow 2 G) (I Y₁ Y₂ Z : Subgroup G) (P : Sylow 2 I)
    (G₁ G₂ : Subgroup I) (hI : IsSQTK K I)
    (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (different : (pCore 2 G₁).map G₁.subtype ≠ (pCore 2 G₂).map G₂.subtype)
    [IsElementaryAbelian 2 Z]
    (hCZ : centralizer (Z : Set G) = (T : Subgroup G))
    (hPT : (P : Subgroup I).map I.subtype ≤ (T : Subgroup G))
    (hB : ChapterB.baumann (T : Subgroup G) ≤ (P : Subgroup I).map I.subtype)
    (hZI : Z ≤ I) (h₁I : Y₁ ≤ I) (h₂I : Y₂ ≤ I)
    (hF : Theory.GroupTheory.generalizedFitting I = pCore 2 I)
    (hgen : Y₁ ⊔ Y₂ ⊔ (P : Subgroup I).map I.subtype = I)
    (h₁ : Y₁ = ⁅Y₁, elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (h₂ : Y₂ = ⁅Y₂, elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hZY : ⁅Z, Y₁⁆ ≠ ⊥) :
    let hC := centralizer_seed_subgroupOf I (T : Subgroup G) Z P T.isPGroup' hPT hZI hCZ
    letI : IsElementaryAbelian 2 (Z.subgroupOf I) := IsElementaryAbelian.subgroupOf hZI
    letI := moduleClosure_elementary P (Z.subgroupOf I) hC hF
    (elementaryAbelianMaxJ (P : Subgroup I)).map coreProjection ≤
        offenderGroup P (Z.subgroupOf I) hC →
      Nonempty ((I ⧸ pCore 2 I) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let hC := centralizer_seed_subgroupOf I (T : Subgroup G) Z P T.isPGroup' hPT hZI hCZ
  let : IsElementaryAbelian 2 (Z.subgroupOf I) := IsElementaryAbelian.subgroupOf hZI
  let := moduleClosure_elementary P (Z.subgroupOf I) hC hF
  change (elementaryAbelianMaxJ (P : Subgroup I)).map coreProjection ≤
    offenderGroup P (Z.subgroupOf I) hC → _
  intro hJ
  exact mixed_symmetricThreeProduct_quotient source618 sourceB T I Y₁ Y₂ Z P
    G₁ G₂ hI triple different hC hB hZI h₁I h₂I hF hgen h₁ h₂ hZY hJ


end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.FullSource
