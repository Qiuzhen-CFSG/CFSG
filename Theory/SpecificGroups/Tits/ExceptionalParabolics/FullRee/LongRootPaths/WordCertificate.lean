module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics

/-!
# Checked Atlas words for the binary Ree long-root path

These four identities use the faithful 1600-point action. The expensive
pointwise checks are isolated here so their full-Ree transports do not repeat
kernel reductions. Source: Parrott (1972), §5, p.683, and the marked
calculation in Aschbacher--Smith J.4.7, printed p.444.
-/

@[expose] public section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.Atlas
abbrev a (i : ParrottGenerator) : Atlas1600Group := atlas1600ParrottAssignment i
def w : Atlas1600Group := a .r8 * a .r1 * a .r8
def leftWord : Atlas1600Group :=
  (a .r1 * a .r8) * atlas1600R5 * (a .r1 * a .r8)⁻¹

private theorem val_mul (x y : Atlas1600Group) : (x*y).val = x.val*y.val := rfl
private theorem val_inv (x : Atlas1600Group) : x⁻¹.val = x.val⁻¹ := rfl
private theorem val_pow (x : Atlas1600Group) (n : ℕ) : (x^n).val = x.val^n := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem fourth_word : w * atlas1600R5 * w⁻¹ = a .s1 := by
  apply Subtype.ext
  simp only [w, a, atlas1600R5_eq, val_mul, val_inv, val_pow,
    atlas1600ParrottAssignment_val]
  apply Equiv.ext
  apply Atlas1600ParrottData.allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem short_word :
    leftWord * a .s1 * leftWord⁻¹ * (a .s1)⁻¹ = a .s7 * a .s4 * (a .s7)⁻¹ := by
  apply Subtype.ext
  simp only [leftWord, a, atlas1600R5_eq, val_mul, val_inv, val_pow,
    atlas1600ParrottAssignment_val]
  apply Equiv.ext
  apply Atlas1600ParrottData.allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem product_four : (leftWord * a .s1)^4 = 1 := by
  apply Subtype.ext
  change (leftWord * a .s1).val ^ 4 = 1
  simp only [leftWord, a, atlas1600R5_eq, val_mul, val_inv, val_pow,
    atlas1600ParrottAssignment_val]
  apply Equiv.ext
  apply Atlas1600ParrottData.allFin
  decide +kernel

theorem product_square_ne : (leftWord * a .s1)^2 ≠ 1 := by
  intro h
  have hh := congrArg (fun x : Atlas1600Group => x.val 0) h
  change ((leftWord * a .s1)^2).val 0 = (0 : Fin 1600) at hh
  revert hh
  simp only [leftWord, a, atlas1600R5_eq, val_mul, val_inv, val_pow,
    atlas1600ParrottAssignment_val]
  decide +kernel

end Tits.ExceptionalParabolics.FullRee.LongRootPaths.Atlas
