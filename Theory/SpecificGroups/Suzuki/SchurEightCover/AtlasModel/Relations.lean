module

public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.Data

/-!
# Checked generator and central-word identities

The four relations used for perfectness are verified on every point. The two
longer words are the last two relators in the first ATLAS presentation of
Sz(8). Their values in this extension are distinct central involutions.
Intermediate word tables avoid repeatedly expanding the same long word.
Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/exc/Sz8/ and `source/README.md`.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.Data

private theorem perm_ext {p q : Equiv.Perm Point}
    (h : checkPoints (fun i => decide (p i = q i)) = true) : p = q :=
  Equiv.ext (of_checkPoints h)

theorem ab_fifth : (a * b) ^ 5 = 1 := by
  apply perm_ext
  decide +kernel

theorem abb_seventh : (a * b ^ 2) ^ 7 = 1 := by
  apply perm_ext
  decide +kernel

private def r : Equiv.Perm Point := a * b * a * b ^ 2 * a * b ^ 2 * a * b⁻¹
private def t : Equiv.Perm Point := a * b * a * b⁻¹ * a * b ^ 2

private theorem r_apply (p : Point) : r p = rFun p := by
  apply of_checkPoints _ p
  decide +kernel

private theorem t_apply (p : Point) : t p = tFun p := by
  apply of_checkPoints _ p
  decide +kernel

private theorem pow_apply_of_apply_eq {α : Type*} (p : Equiv.Perm α) (f : α → α)
    (h : ∀ x, p x = f x) (n : ℕ) (x : α) : (p ^ n) x = f^[n] x := by
  rw [Equiv.Perm.coe_pow]
  exact congrArg (fun g : α → α => g^[n] x) (funext h)

theorem z_word : z = (a * b * a * b ^ 2 * a * b ^ 2 * a * b⁻¹) ^ 5 := by
  change z = r ^ 5
  apply Equiv.ext
  intro p
  rw [pow_apply_of_apply_eq r rFun r_apply]
  apply of_checkPoints _ p
  decide +kernel

theorem w_word : w = (a * b * a * b⁻¹ * a * b ^ 2) ^ 7 := by
  change w = t ^ 7
  apply Equiv.ext
  intro p
  rw [pow_apply_of_apply_eq t tFun t_apply]
  apply of_checkPoints _ p
  decide +kernel

theorem z_commute_a : Commute z a := by
  apply perm_ext
  decide +kernel

theorem z_commute_b : Commute z b := by
  apply perm_ext
  decide +kernel

theorem w_commute_a : Commute w a := by
  apply perm_ext
  decide +kernel

theorem w_commute_b : Commute w b := by
  apply perm_ext
  decide +kernel

theorem z_ne_one : z 0 ≠ 0 := by decide +kernel
theorem w_ne_one : w 0 ≠ 0 := by decide +kernel
theorem z_ne_w : z 0 ≠ w 0 := by decide +kernel

end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.Data
