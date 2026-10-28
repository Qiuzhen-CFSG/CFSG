module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.ClassifiedGroups
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Adequate.Components
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ExhaustiveSource

/-!
# Selecting the marked factors from the corrected adequate alternatives

Two distinct components exclude quasisimple F* and the group-only outer
shape. The other alternatives retain their complete module data, so the
proved factor-selection argument applies verbatim. The two component
inclusions and the original quotient-module records are preserved.

Source: Aschbacher–Smith, B.5.6, p.105; 13.8.16(1), case (a), p.952
(combined manuscript, 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.ClassifiedGroups
universe u v
variable {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- The full marked two-factor conclusion from both source corrections,
on the same actor and representation. -/
theorem exists_marked_twoFactorCase_of_adequate {K : GroupClass.{u}}
    (hyp : FFHypothesis K ρ) (hclass : ProjectiveLine.AdequateSourceAlternative ρ)
    {A B : Subgroup D} (hA : IsComponent D A) (hB : IsComponent D B) (hne : A ≠ B)
    (hfull : Representation.BinaryOffender.subspaceCommutator ρ ⊤ (A ⊔ B) = ⊤) :
    ∃ c : SourceTwoFactorCase ρ, A ≤ c.first ∧ B ≤ c.second := by
  cases hclass with
  | trivial ht => exact exists_marked_twoFactorCase ρ hyp (.trivial ht) hA hB hne hfull
  | quasisimple hq _ =>
    have hf : IsComponent D (generalizedFitting D) :=
      ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal, hq⟩
    exact (hne ((hA.eq_of_le hf (component_le_generalizedFitting D A hA)).trans
      (hB.eq_of_le hf (component_le_generalizedFitting D B hB)).symm)).elim
  | symmetricThree c =>
    exact exists_marked_twoFactorCase ρ hyp (.symmetricThree c) hA hB hne hfull
  | twoFactors c => exact exists_marked_twoFactorCase ρ hyp (.twoFactors c) hA hB hne hfull
  | outerSixThree c => exact (hne (outerSixThreeShape_components_eq c hA hB)).elim
  | hyperplane c => exact exists_marked_twoFactorCase ρ hyp (.hyperplane c) hA hB hne hfull

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.ClassifiedGroups
