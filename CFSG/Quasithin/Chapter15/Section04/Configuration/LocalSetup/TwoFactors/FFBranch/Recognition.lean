module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ActionGroup
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.SeedCriterion
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.SectionAlternatives
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ExceptionalFixedSpace.BinaryG2
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ExceptionalFixedSpace.TripleSix
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.Quotient

/-!
# Recognition of the mixed FF quotient

The two raw factor identities, transported using Baumann containment, place
both factor images in the actual best-offender subgroup. The descendants
construct that group's B.5.3 inputs and the precise Sylow fixed-space test.

The classification comparison now supplies an exhaustive group and source
module disjunction. Native moved-section calculations exclude the ordinary
linear, alternating and symplectic models using the original seed centralizer.
The marked binary G₂ and F₄-linear triple-six sections are also excluded,
including their actual subgroup actions and both module extensions. The
triple-six calculation uses the actual central quotient to A₆ and a cubic
fixer in the given representation. Combining these exclusions with the
proved source-row extraction establishes `I/O₂(I) ≃ S₃ × S₃`.

The full universal F.6.18 and corrected B.5.1/adequate B.5.6 inputs, the
Thompson-image containment, and the preceding mixed source data remain
explicit. F.6.11 is discharged by its elementary proof. The parent retains
the final source-hypothesis discharge and normalizer contradiction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 15.4.18, printed pp.1162–1163.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open Subgroup Stellmacher
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Both factor images lie in the actual offender group, using only the raw
commutator identities. No full T-invariant family membership is imposed on Y₂. -/
theorem mixed_factor_images_le_offenderGroup
    (T : Sylow 2 G) (I Y₁ Y₂ Z : Subgroup G) (P : Sylow 2 I)
    [IsElementaryAbelian 2 (moduleClosure (Z.subgroupOf I))]
    (hC : centralizer (Z.subgroupOf I : Set I) = (P : Subgroup I))
    (hB : ChapterB.baumann (T : Subgroup G) ≤ (P : Subgroup I).map I.subtype)
    (h₁I : Y₁ ≤ I) (h₂I : Y₂ ≤ I)
    (h₁ : Y₁ = ⁅Y₁, elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (h₂ : Y₂ = ⁅Y₂, elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hJ : (elementaryAbelianMaxJ (P : Subgroup I)).map coreProjection ≤
      offenderGroup P (Z.subgroupOf I) hC) :
    (Y₁.subgroupOf I).map coreProjection ≤ offenderGroup P (Z.subgroupOf I) hC ∧
      (Y₂.subgroupOf I).map coreProjection ≤ offenderGroup P (Z.subgroupOf I) hC := by
  have hJT := thompson_sylow_image_of_baumann I T P hB
  exact ⟨factor_image_le_offenderGroup P (Z.subgroupOf I) hC _
      (factor_commutator_subgroupOf I Y₁ _ _ h₁I hJT h₁) hJ,
    factor_image_le_offenderGroup P (Z.subgroupOf I) hC _
      (factor_commutator_subgroupOf I Y₂ _ _ h₂I hJT h₂) hJ⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
