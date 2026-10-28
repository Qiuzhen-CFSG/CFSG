module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.RootDuality

/-!
# A geometric bound for F4 divided powers

Every F4 root has squared length one or two. The parallelogram identity then
bounds the squared distance between two roots by eight, whereas three times a
root has squared length at least nine. Thus a three-step root displacement
cannot occur. This is the geometric vanishing criterion for the cubic term in
Geck's simple-root divided powers; it applies to both signs and both lengths.
-/

public section

namespace ReeF4.WordRelations

open Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators

private theorem root_norm_bounds (r : typeF4Roots) :
    1 ≤ dot r.val r.val ∧ dot r.val r.val ≤ 2 := by
  by_cases hr : IsLongRoot r
  · rw [isLongRoot_norm r hr]
    norm_num
  · rw [isShortRoot_norm r hr]
    norm_num

/-- No two F4 roots differ by three times a root. -/
theorem root_ne_add_three_smul (i j k : typeF4Roots) :
    k.val ≠ j.val + (3 : ℝ) • i.val := by
  intro h
  have hpos : 0 ≤ dot (k.val + j.val) (k.val + j.val) := by
    exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  have hdiff : dot (k.val - j.val) (k.val - j.val) = 9 * dot i.val i.val := by
    have hd : k.val - j.val = (3 : ℝ) • i.val := by rw [h]; abel
    rw [hd]
    change ((3 : ℝ) • i.val) ⬝ᵥ ((3 : ℝ) • i.val) = 9 * (i.val ⬝ᵥ i.val)
    rw [smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  have hpar : dot (k.val - j.val) (k.val - j.val) +
      dot (k.val + j.val) (k.val + j.val) =
      2 * (dot k.val k.val + dot j.val j.val) := by
    change (k.val - j.val) ⬝ᵥ (k.val - j.val) +
      (k.val + j.val) ⬝ᵥ (k.val + j.val) = 2 * (k.val ⬝ᵥ k.val + j.val ⬝ᵥ j.val)
    simp only [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add]
    ring
  nlinarith [(root_norm_bounds i).1, (root_norm_bounds j).2, (root_norm_bounds k).2]

/-- The natural-scalar form used in `eDividedPower`'s matrix entries. -/
theorem root_ne_add_three_nsmul (i j k : typeF4Roots) :
    typeF4RootPairing.root k ≠
      typeF4RootPairing.root j + (3 : ℕ) • typeF4RootPairing.root i := by
  simpa only [typeF4RootPairing_root, ofNat_smul_eq_nsmul] using
    root_ne_add_three_smul i j k

end ReeF4.WordRelations
