module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.GoldschmidtReduction
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree
/-!
# The proved elementary source of F.6.11

The general finite Goldschmidt-triple theorem in Chapter F supplies the entire
existing F.6.11 interface. Its local kernel identities give canonical quotient
maps for all three amalgam terms. In the collapsed case the native supplement
and noncyclicity results retain the full source conclusion. No SQTK or module
hypothesis is required, and the three-prime core is not identified with the
two-core by this adapter.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, F.6.11, printed pp.306–307.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {H : Type u} [Group H] [Finite H]

private theorem compatible_of_elementary {G₁ G₂ : Subgroup H}
    (h : ChapterF.IsGoldschmidtTriple G₁ G₂) (M : Subgroup H) (hM : M ≤ G₁) :
    CompatibleThreePrimeQuotient M := by
  apply compatibleThreePrimeQuotient_of_kernel
  simpa only [ker_subgroupMap, QuotientGroup.ker_mk'] using
    h.primeToThreeCore_subgroup_kernel M hM

/-- The complete F.6.11 conclusion from a genuine finite Goldschmidt triple. -/
theorem f611Conclusion_of_goldschmidt {G₁ G₂ : Subgroup H}
    (h : ChapterF.IsGoldschmidtTriple G₁ G₂) : F611Conclusion G₁ G₂ := by
  obtain ⟨hs, hsol⟩ := h.primeToThreeCore_structure
  refine ⟨hs, hsol, ?_⟩
  rcases h.primeToThreeCore_image_intersection_or_eq with hi | he
  · exact Or.inl ⟨hi, h.quotient_primeToThreeCore_of_intersection hi,
      h.primeToThreeCore_quotient_twoCore_eq_bot,
      compatible_of_elementary h G₁ le_rfl,
      compatible_of_elementary h (G₁ ⊓ G₂) inf_le_left,
      compatible_of_elementary h.symm G₂ le_rfl⟩
  · obtain ⟨h₁, h₂, eqv, _, _⟩ := h.primeToThreeCore_collapsed_structure he
    exact Or.inr ⟨h₁, h₂, eqv, (h.primeToThreeCore_collapsed_sup he).1,
      h.primeToThreeCore_collapsed_noncyclic he⟩

/-- The existing universal interface is discharged on its full finite-triple domain. -/
theorem f611Universal_of_elementary : F611Universal.{u} :=
  fun _ _ h => f611Conclusion_of_goldschmidt h
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
