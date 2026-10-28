module
public import Theory.SpecificGroups.G2.TernaryLevi

/-!
# A determinant cocycle for the ternary Levi group

The abelianization of SL₂(3) supplies a ternary cocycle on GL₂(3), with
its determinant action on the target. The explicit 48-element table below
is checked on all pairs of invertible two-by-two matrices. The cocycle is
one on the positive cubic and zero on the chosen Weyl involution.

TernaryEndpointShifts uses this cocycle to extend the central simple-root
shifts across the two full parabolics, for the I.4.5 amalgam comparison.
Source: Aschbacher–Smith I.4.5, p.417, via F.4.26, p.288. The imported
ATLAS model retains LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
namespace Atlas.G2.TernaryLevi
private abbrev M := Matrix (Fin 2) (Fin 2) (ZMod 3)
private def shiftCode : Nat → ZMod 3
  | 34 | 25 | 78 | 47 | 37 | 48 | 74 | 22 | 39 | 35 | 17 | 69 | 58 | 64 | 14 | 59 => 1
  | 31 | 51 | 26 | 46 | 73 | 42 | 16 | 75 | 23 | 61 | 13 | 38 | 32 | 62 | 65 | 66 => -1
  | _ => 0
private def shiftMatrix (a : M) : ZMod 3 :=
  shiftCode ((a 0 0).val+3*(a 0 1).val+9*(a 1 0).val+27*(a 1 1).val)
def shiftCocycle (a : GL23) : ZMod 3 := shiftMatrix a.val
private theorem shiftMatrix_mul : ∀ a b : M, a.det≠0 → b.det≠0 →
    shiftMatrix (a*b)=shiftMatrix a+a.det*shiftMatrix b := by decide +kernel

theorem shiftCocycle_mul (a b : GL23) :
    shiftCocycle (a*b)=shiftCocycle a+a.val.det*shiftCocycle b :=
  shiftMatrix_mul a.val b.val (Units.ne_zero (Matrix.GeneralLinearGroup.det a))
    (Units.ne_zero (Matrix.GeneralLinearGroup.det b))

@[simp] theorem shiftCocycle_one : shiftCocycle 1=0 := by decide +kernel
@[simp] theorem shiftCocycle_generator (b : Bool) :
    shiftCocycle (generator b)=if b then 0 else 1 := by cases b <;> decide +kernel
/-- The cocycle vanishes on the entire diagonal torus. -/
theorem shiftCocycle_diagonal (a : GL23) (h01 : a.val 0 1=0) (h10 : a.val 1 0=0) :
    shiftCocycle a=0 := by
  have h : ∀ a : M,a 0 1=0 → a 1 0=0 → shiftMatrix a=0 := by decide +kernel
  exact h a.val h01 h10
end Atlas.G2.TernaryLevi
