module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.SectionAlternatives.Source
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ExceptionalFixedSpace.BinaryG2
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ExceptionalFixedSpace.TripleSix
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Residual

/-!
# Recognition of the mixed FF quotient

The exhaustive comparison gives either an actual S₃ × S₃ quotient or a
quasisimple branch on its actual offender subgroup. Source-row extraction
and the ordinary and binary G₂ fixed-space calculations reduce the latter
branch to the genuine triple-six section. Its cubic fixer contradicts the
seed centralizer, including through both module extensions.

The intrinsic and ambient applications retain the complete universal
F.6.18 and corrected B.5.1/adequate B.5.6 inputs. F.6.11, the equality
O_{3′}(I) = O₂(I), every module exclusion, and the quotient identification
are proved. The Thompson-image containment remains the authorized input
from the offender-factorization owner. The parent supplies the preceding
mixed source configuration and uses the identification for the final
normalizer contradiction. No full T-invariant family membership is required
of the second factor, and the offender subgroup is not assumed to be the
whole quotient.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the final
paragraph of Lemma 15.4.18, printed p.1163; F.6.11/F.6.18, pp.306–310;
B.5.1/B.5.3/B.5.6, pp.99–110.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open ClassificationComparison
universe u
variable {H : Type u} [Group H] [Finite H]

/-- No quasisimple comparison branch survives on the literal quotient action.
The section disjunction and every fixed-space calculation are discharged. -/
theorem quotientAction_not_comparedBranch
    (P : Sylow 2 H) (Z : Subgroup H) [IsElementaryAbelian 2 (moduleClosure Z)]
    (hC : centralizer (Z : Set H) = (P : Subgroup H)) :
    ¬ Nonempty (QuasisimpleComparison.ComparedBranch (quotientAction P Z hC)) := by
  rintro ⟨b⟩
  obtain ⟨hf, hSix⟩ := comparedBranch_tripleSix_of_models P Z hC b b.sectionAlternatives
  exact comparedBranch_not_tripleSix P Z hC b hf hSix

/-- Recognize the original two-core quotient from the intrinsic mixed data.
The comparison proves the kernel equality before identifying the quotient. -/
theorem symmetricThreeProduct_quotient_of_goldschmidt {K : GroupClass.{u}}
    (source618 : F618Universal K)
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
  obtain ⟨_, _, _, h⟩ := exhaustive_comparison_of_goldschmidt source618 sourceB
    hH G₁ G₂ triple different P Z Y₁ Y₂ hC hF hgen h₁ h₂ hZY hJ
  exact h.resolve_right (quotientAction_not_comparedBranch P Z hC)

/-- The identification used in 15.4.18 on the actual ambient factors inside I.
Baumann containment transports both raw commutator identities into I. -/
theorem mixed_symmetricThreeProduct_quotient
    {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
    (source618 : F618Universal K)
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
  obtain ⟨_, _, _, h⟩ := mixed_exhaustive_comparison source618 sourceB T I Y₁ Y₂ Z P
    G₁ G₂ hI triple different hC hB hZI h₁I h₂I hF hgen h₁ h₂ hZY hJ
  exact h.resolve_right (quotientAction_not_comparedBranch P (Z.subgroupOf I) hC)

/-- Start with the ambient elementary seed and its original centralizer.
Construct the internal centralizer and elementary conjugate-span module;
only the authorized Thompson-image containment remains to be supplied. -/
theorem mixed_symmetricThreeProduct_quotient_of_ambient_seed
    {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
    (source618 : F618Universal K)
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

/-- The recognized quotient and the source normalizer contradiction compose into
the actual characteristic-two branch elimination.  Every mixed-configuration
hypothesis remains explicit: the quotient theorem supplies only the genuine
`S₃ × S₃` witness, and the residual argument discharges the resulting
normalization before it is lifted back to the ambient group. -/
theorem mixed_symmetricThreeProduct_contradiction
    {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
    (source618 : F618Universal K)
    (sourceB : FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u} K)
    (T : Sylow 2 G) (I Y₁ Y₂ Z : Subgroup G) (P : Sylow 2 I)
    (G₁ G₂ : Subgroup I) (hI : IsSQTK K I)
    (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (different : (pCore 2 G₁).map G₁.subtype ≠ (pCore 2 G₂).map G₂.subtype)
    [IsElementaryAbelian 2 (moduleClosure (Z.subgroupOf I))]
    (hC : centralizer (Z.subgroupOf I : Set I) = (P : Subgroup I))
    (hPT : (P : Subgroup I).map I.subtype ≤ (T : Subgroup G))
    (hB : ChapterB.baumann (T : Subgroup G) ≤ (P : Subgroup I).map I.subtype)
    (hZI : Z ≤ I) (h₁I : Y₁ ≤ I) (h₂I : Y₂ ≤ I)
    (hF : Theory.GroupTheory.generalizedFitting I = pCore 2 I)
    (hgen : Y₁ ⊔ Y₂ ⊔ (P : Subgroup I).map I.subtype = I)
    (h₁ : Y₁ = ⁅Y₁, elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (h₂ : Y₂ = ⁅Y₂, elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hZY : ⁅Z, Y₁⁆ ≠ ⊥)
    (hJ : (elementaryAbelianMaxJ (P : Subgroup I)).map coreProjection ≤
      offenderGroup P (Z.subgroupOf I) hC)
    (hperfect : IsPPerfect 2 Y₁)
    (hTnorm : (T : Subgroup G) ≤ normalizer (Y₁ : Set G))
    (hnot : ¬ Y₂ ≤ normalizer (Y₁ : Set G)) : False := by
  obtain ⟨e⟩ := mixed_symmetricThreeProduct_quotient source618 sourceB T I Y₁ Y₂ Z P
    G₁ G₂ hI triple different hC hB hZI h₁I h₂I hF hgen h₁ h₂ hZY hJ
  have hJ' := thompson_sylow_image_of_baumann I T P hB
  have h₁' := factor_commutator_subgroupOf I Y₁ _ _ h₁I hJ' h₁
  have h₂' := factor_commutator_subgroupOf I Y₂ _ _ h₂I hJ' h₂
  have hp : IsPPerfect 2 (Y₁.subgroupOf I) := hperfect.of_surjective
    (subgroupOfEquivOfLe h₁I).symm.toMonoidHom (subgroupOfEquivOfLe h₁I).symm.surjective
  have hQnorm : pCore 2 I ≤ normalizer (Y₁.subgroupOf I : Set I) := by
    rw [← subgroupOf_normalizer_eq h₁I]
    intro x hx
    exact hTnorm (hPT (mem_map_of_mem I.subtype
      (pCore_isPGroup.le_sylow_of_normal P hx)))
  have hn := normalizes_factor_of_symmetricThreeProduct_quotient (pCore 2 I)
    (Y₁.subgroupOf I) (Y₂.subgroupOf I) (elementaryAbelianMaxJ (P : Subgroup I))
    pCore_isPGroup hp hQnorm h₁' h₂' e
  exact hnot (normalizer_subgroupOf_lift I Y₁ Y₂ h₁I h₂I hn)


end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
