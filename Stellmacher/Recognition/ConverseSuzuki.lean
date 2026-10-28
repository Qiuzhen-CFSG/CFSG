module

public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import BenderSuzuki.MatrixGroups.SuzukiModel
public import Theory.GroupTheory.MinimalSimple
public import Theory.SpecificGroups.Suzuki.ProperSubgroups

/-!
# Minimal simplicity of Suzuki groups at prime exponents

When `2 * n + 1` is prime, the concrete Suzuki group is simple and
nonsolvable, and every proper subgroup is solvable. The proper-subgroup
theorem recognizes a nonsolvable subgroup as a positive-parameter Suzuki
group and excludes such proper subgroups at prime ambient degree.
Equality of the matrix-generated models transfers this result to `SzModel`.

Source: Huppert--Blackburn, *Finite Groups III*, XI.3.6 and XI.3.12(e),
with nonsolvable-subgroup recognition from XI.11.15; Thompson's Suzuki
family in the minimal-simple classification.
-/

namespace Stellmacher.Recognition

open BenderSuzuki.MatrixGroups BenderSuzuki.External

/-- A concrete Suzuki matrix group at prime odd degree is minimal simple. -/
public theorem isMinimalSimple_suzuki_matrix {n : ℕ} (hn : Nat.Prime (2 * n + 1)) :
    IsMinimalSimple (SuzukiMatrixGroup n) := by
  have hnpos : 0 < n := by have := hn.two_le; omega
  refine ⟨(huppert_blackburn_XI_3_6 n hnpos).1,
    suzukiMatrixGroup_not_isSolvable n hnpos, ?_⟩
  intro H hH
  exact suzukiMatrixGroup_proper_subgroup_isSolvable hn H (ne_of_lt hH)

/-- Thompson's Suzuki family is minimal simple at prime odd degree. -/
public theorem isMinimalSimple_suzuki {n : ℕ} (hn : Nat.Prime (2 * n + 1)) :
    IsMinimalSimple (SzModel n) := by
  rw [szModel_eq_suzukiMatrixGroup]
  exact isMinimalSimple_suzuki_matrix hn

end Stellmacher.Recognition
