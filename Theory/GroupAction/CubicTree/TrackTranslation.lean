module

public import Theory.GroupAction.CubicTree.Tracks

/-!
# Integer translations along the original track

Every integer power of the selected translation moves a vertex by twice that
integer. This fixes the left-action convention for the normalizer argument and
the conjugate central intervals in Goldschmidt Sections 5--6.
-/

@[expose] public section
namespace Theory.GroupAction.CubicTree
open SimpleGraph
universe u v
variable {V : Type u} {G : Type v} {Γ : SimpleGraph V} [Group G] [MulAction G V]
namespace Track

theorem zpow_translate (t : Track Γ G) (k i : ℤ) :
    t.translation ^ k • t.vertex i = t.vertex (i + 2 * k) := by
  induction k using Int.induction_on generalizing i with
  | zero => simp only [zpow_zero, one_smul, mul_zero, add_zero]
  | succ k ih =>
    rw [zpow_add, zpow_one, mul_smul, t.translate, ih]
    congr 1
    omega
  | pred k ih =>
    rw [zpow_sub, zpow_one, mul_smul, t.inverse_translate, ih]
    congr 1
    omega

end Track
end Theory.GroupAction.CubicTree
