module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ActionGroup
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.SeedCriterion
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.Inputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SymmetricThree
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SylowBound
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.Exhaustive

/-!
# The exhaustive Goldschmidt and FF classification comparison

The actual offender subgroup satisfies B.5.3. The proved general F.6.11 theorem
preserves the Goldschmidt triple when the embedded local two-cores differ.
The full B.5.1/B.5.6 inputs eliminate the offender group's three-prime core;
together with F.6.11 this proves O_{3'}(H)=O₂(H). `Prepared` therefore places
all surviving F.6.18 rows on the actual action quotient, retaining every FF
module alternative on the actual offender subgroup. `SymmetricThree` excludes
the trivial and single-S₃ actors, and `SylowBound` bounds every ambient Sylow
two-subgroup by 128. The old conditional
`prepare` interface remains available alongside `prepare_of_goldschmidt`.

`exhaustive_comparison_of_goldschmidt` reduces the complete source lists to
an actual S₃ × S₃ quotient equivalence or concrete small offender and ambient
models with all surviving module extensions. The small actors are L₃(2), A₆,
S₆, A₇, S₇, the triple-six cover, G₂(2)′ and G₂(2); the ambient catalogue
also retains the triple-symmetric-six cover. The actual offender subgroup
is never identified with the entire quotient without proof.

The source-facing classifier uses the corrected triple-six projective line
and the adequate outer A₆–C₃ group configuration. The latter is excluded
without a fixed-space splitting assumption. Full universal F.6.18 and
B.5.1/adequate B.5.6 remain explicit authorized source inputs. The stronger
old conditional APIs below are preserved. Concrete module exclusions and
the final S₃ × S₃ identification remain with the recognition owner.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, final paragraph of 15.4.18, printed p.1163.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {H : Type u} [Group H] [Finite H]

/-- Assemble the established comparison inputs from the intrinsic mixed data.
The full F.6.11 implication is an explicit source input; the last implication
records the remaining classification obligation for the kernel bridge. -/
theorem prepare (source : F611Universal.{u}) {K : GroupClass.{u}} (hH : IsSQTK K H)
    (G₁ G₂ : Subgroup H) (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
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
    F611Preserved G₁ G₂ ∧
      FFHypothesis K (offenderAction P Z hC) ∧
      IsFFModule (offenderAction P Z hC) ∧
      IsPGroup 2 (coreQuotient H ⧸ offenderGroup P Z hC) ∧
      (pPrimeCore 3 (offenderGroup P Z hC) = ⊥ → pPrimeCore 3 H = pCore 2 H) := by
  obtain ⟨⟨S, hS⟩, _, hp⟩ := apply_F611_of_different_cores source G₁ G₂ triple different
  obtain ⟨hb, hw⟩ := offenderFFHypothesis_and_witness P Z hC hH Y₁ hF h₁ hZY
  have hq := quotient_offenderGroup_isTwoGroup P Z hC Y₁ Y₂ hgen h₁ h₂ hJ
  exact ⟨hp, hb, hw, hq, threePrimeCore_eq_twoCore_of_offender_core P Z hC S hS hq⟩

/-- Source-facing preparation: the full F.6.11 implication is proved from the
finite Goldschmidt triple, with exactly the other hypotheses and conclusions
of `prepare`. -/
theorem prepare_of_goldschmidt {K : GroupClass.{u}} (hH : IsSQTK K H)
    (G₁ G₂ : Subgroup H) (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
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
    F611Preserved G₁ G₂ ∧
      FFHypothesis K (offenderAction P Z hC) ∧
      IsFFModule (offenderAction P Z hC) ∧
      IsPGroup 2 (coreQuotient H ⧸ offenderGroup P Z hC) ∧
      (pPrimeCore 3 (offenderGroup P Z hC) = ⊥ → pPrimeCore 3 H = pCore 2 H) :=
  prepare f611Universal_of_elementary hH G₁ G₂ triple different P Z Y₁ Y₂ hC hF
    hgen h₁ h₂ hZY hJ

/-- The original stronger conditional reductions, retaining their public
interface. The source-facing exhaustive comparison is exported separately
by `exhaustive_comparison_of_goldschmidt`. -/
theorem comparison_reductions_of_goldschmidt {K : GroupClass.{u}}
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
        (G₁.map coreProjection) (G₂.map coreProjection) ∧
      RemainingFFAlternative (offenderAction P Z hC) ∧
      (∀ S : Sylow 2 (coreQuotient H), Nat.card S ≤ 128) := by
  obtain ⟨hk, hp, h⟩ := classifiedAction_of_goldschmidt source618 sourceB hH G₁ G₂
    triple different P Z Y₁ Y₂ hC hF hgen h₁ h₂ hZY hJ
  exact ⟨hk, hp, h, h.remaining_ff, h.sylow_card_le⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
