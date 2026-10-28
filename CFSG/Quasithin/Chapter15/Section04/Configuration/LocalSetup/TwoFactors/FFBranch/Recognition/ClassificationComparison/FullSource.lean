module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FullSource.Preparation
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FullSource.Recognition

/-!
# Mixed FF comparison from the full Goldschmidt source

The corrected thirteen source rows and two field extensions are compared
with the full adequate projective-line FF alternatives on the actual offender
action. The nonquasisimple rows give the symmetric-three product. In the
quasisimple case, the bounded small actor and all source module alternatives
feed the seed-centralizer fixed-space exclusions. The comparison therefore
returns the quotient identification, retaining the original quotient maps.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.6.18, pp.309–310; B.5.1/B.5.6, pp.99–110; 15.4.18, p.1163.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FullSource
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {H : Type u} [Group H] [Finite H]

/-- Full-source comparison on the intrinsic quotient and its literal action. -/
theorem exhaustive_comparison_of_goldschmidt {K : GroupClass.{u}}
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
        (G₁.map coreProjection) (G₂.map coreProjection)) ∧
      ExhaustiveComparison (quotientAction P Z hC) := by
  obtain ⟨hk, hp, h⟩ := classifiedAction_of_adequate_goldschmidt
    source618 sourceB hH G₁ G₂ triple different P Z Y₁ Y₂ hC hF hgen h₁ h₂ hZY hJ
  obtain ⟨h⟩ := h
  exact ⟨hk, hp, ⟨h⟩, Or.inl (h.quotient_equiv P Z hC)⟩


/-- Apply the corrected comparison to the original ambient mixed factors. -/
theorem mixed_exhaustive_comparison
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
    (h₁ : Y₁ = ⁅Y₁, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (h₂ : Y₂ = ⁅Y₂, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hZY : ⁅Z, Y₁⁆ ≠ ⊥)
    (hJ : (Stellmacher.elementaryAbelianMaxJ (P : Subgroup I)).map coreProjection ≤
      offenderGroup P (Z.subgroupOf I) hC) :
    pPrimeCore 3 I = pCore 2 I ∧ F611Preserved G₁ G₂ ∧
      Nonempty (ClassifiedAction K (quotientAction P (Z.subgroupOf I) hC)
        (G₁.map coreProjection) (G₂.map coreProjection)) ∧
      ExhaustiveComparison (quotientAction P (Z.subgroupOf I) hC) := by
  have hJT := thompson_sylow_image_of_baumann I T P hB
  have hgen' : Y₁.subgroupOf I ⊔ Y₂.subgroupOf I ⊔ (P : Subgroup I) = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup, map_subgroupOf_eq_of_le h₁I,
      map_subgroupOf_eq_of_le h₂I, ← MonoidHom.range_eq_map, I.range_subtype]
    exact hgen
  exact exhaustive_comparison_of_goldschmidt source618 sourceB hI G₁ G₂ triple different
    P (Z.subgroupOf I) (Y₁.subgroupOf I) (Y₂.subgroupOf I) hC hF hgen'
    (factor_commutator_subgroupOf I Y₁ _ _ h₁I hJT h₁)
    (factor_commutator_subgroupOf I Y₂ _ _ h₂I hJT h₂)
    (seed_factor_commutator_ne_bot_subgroupOf I Z Y₁ hZI h₁I hZY) hJ


end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FullSource
