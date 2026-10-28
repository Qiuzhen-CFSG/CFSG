module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.MixedLocal
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.GoldschmidtAlternatives
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ElementarySource
public import Theory.GroupTheory.PCoreImage

/-!
# Classification rows for the actual mixed star quotient

Transport the unequal embedded local two-cores into the generated group I.
The proved F.6.11 theorem then gives the preserved Goldschmidt triple in
I/O_{3′}(I). The universal F.6.18 row input places that literal quotient
on the retained list in either source labeling; the first row is excluded
by the unequal cores. All other rows remain, including covers, field and
graph extensions and their parameter restrictions.

The reused row interface permits every extension by E₄ of the extraspecial
three-group in row (2), forgetting the particular source action. This is a
weaker classification consequence, sufficient for a component argument only
when that entire solvable extension case is excluded. The source owner must
still prove the actual action clause in the native classification theorem.
This adapter proves no identification of the original component or of a
quotient by a residual.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, F.6.11,
pp.306–307; F.6.18, pp.309–310; proof of 15.4.18, printed pp.1162–1163.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch
open MixedLocal FFBranch.ClassificationComparison
variable {G : Type*} [Group G] [Finite G]

/-- Apply the universal F.6.18 row interface to the literal star quotient of the
constructed mixed group. F.6.11 is discharged by its proved elementary theorem;
only row (1) is removed, by the unequal actual local cores. -/
theorem mixed_classification_rows
    {K : GroupClass} (source : F618Universal K)
    (T : Sylow 2 G) {Y X M₂ : Subgroup G} {F : Bool → Subgroup G}
    (c : Configuration K T Y X M₂ F) :
    let A := (firstGroup T Y F).subgroupOf (generated T Y F)
    let B := (secondGroup T F).subgroupOf (generated T Y F)
    F611Conclusion A B ∧
      GoldschmidtAlternatives.Remaining (threePrimeImage A) (threePrimeImage B) := by
  let I := generated T Y F
  let A := (firstGroup T Y F).subgroupOf I
  let B := (secondGroup T F).subgroupOf I
  have hk : IsPGroup 2 I.subtype.ker := by
    rw [ker_subtype]
    exact IsPGroup.of_bot
  have hne : A.pCoreIn 2 ≠ B.pCoreIn 2 := by
    intro he
    apply c.different_cores
    have h := congrArg (Subgroup.map I.subtype) he
    rw [map_pCoreIn_of_ker_isPGroup I.subtype hk,
      map_pCoreIn_of_ker_isPGroup I.subtype hk,
      map_subgroupOf_eq_of_le (show firstGroup T Y F ≤ I from le_sup_left),
      map_subgroupOf_eq_of_le (show secondGroup T F ≤ I from le_sup_right)] at h
    exact h
  exact ⟨f611Conclusion_of_goldschmidt c.goldschmidt,
    (apply_F618_of_different_cores f611Universal_of_elementary source c.sqtk
      A B c.goldschmidt hne).2⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch
