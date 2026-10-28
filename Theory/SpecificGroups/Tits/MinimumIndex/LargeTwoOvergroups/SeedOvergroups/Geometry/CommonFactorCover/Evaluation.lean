module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.Membership

/-!
# Packed inverse evaluation for common-factor certificates

The original packed forward maps are unchanged. Inverses use the same forward
map for involutions and its cube for the three generators of order four.
A kernel check at every point certifies the inverse law. The resulting place
and row evaluators are proved equal to the existing literal evaluators.
Source: Parrott (1972), §5, p.683, relators (I).
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover
open OuterOddSubgroups.OverlapCentralizers
set_option Elab.async false

def backward (i : Fin 10) (p : Fin 1600) : Fin 1600 :=
  if i = 4 ∨ i = 6 ∨ i = 8 then
    Packed.pointMap i (Packed.pointMap i (Packed.pointMap i p))
  else Packed.pointMap i p

set_option maxRecDepth 20000 in
theorem backward_right (i : Fin 10) (p : Fin 1600) :
    Packed.pointMap i (backward i p) = p := by
  revert i p
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

def perm (i : Fin 10) : Equiv.Perm (Fin 1600) where
  toFun := Packed.pointMap i
  invFun := backward i
  right_inv := backward_right i
  left_inv p := by
    apply (Packed.perm i).injective
    exact backward_right i (Packed.pointMap i p)

theorem perm_eq (i : Fin 10) : perm i = Packed.perm i := Equiv.ext (fun _ => rfl)

def assignment : ParrottGenerator → Equiv.Perm (Fin 1600)
  | .r1 => perm 0
  | .r8 => perm 1
  | .s1 => perm 2
  | .s2 => perm 3
  | .s3 => perm 4
  | .s4 => perm 5
  | .s5 => perm 6
  | .s6 => perm 7
  | .s7 => perm 8
  | .s8 => perm 9

def conjugator (j : Fin 38) := ((placeWord j).map assignment).prod

def test (g : Equiv.Perm (Fin 1600)) (j : Fin 38) : Bool :=
  let w := conjugator j
  let a := w⁻¹ * g * w
  if j.val < 17 then sameBase (a * centralPerm) (centralPerm * a)
  else centerImageTest a centralPerm && centerImageTest a matePerm



theorem assignment_eq (s : ParrottGenerator) : assignment s = fastAssignment s := by
  cases s <;> simp only [assignment, fastAssignment, perm_eq]

theorem conjugator_eq (j : Fin 38) : conjugator j = fastConjugator j := by
  unfold conjugator fastConjugator
  rw [show assignment = fastAssignment from funext assignment_eq]

theorem test_eq (g : Equiv.Perm (Fin 1600)) (j : Fin 38) :
    test g j = placeTest g j := by
  simp only [test, placeTest, conjugator_eq]

/-- The optimized test has precisely the existing subgroup-membership meaning. -/
theorem test_iff (g : Atlas1600Group) (j : Fin 38) :
    test g.val j = true ↔ g ∈ place j := by
  rw [test_eq, placeTest_iff]

/-- Evaluate the original row word with certified packed inverses. -/
def row (r : Row) : Equiv.Perm (Fin 1600) :=
  let j : Fin 38 := ⟨r.1 % 38, Nat.mod_lt _ (by decide)⟩
  let n : Fin 2048 := ⟨r.1 / 38 % 2048, Nat.mod_lt _ (by decide)⟩
  let rotation := if j.val < 17 then fastAssignment .s1 * fastAssignment .r1
    else fastAssignment .s8 * fastAssignment .r8
  let w := conjugator j
  w * (fastNormalForm n * rotation ^ (r.1 / (38 * 2048))) * w⁻¹

theorem row_eq (r : Row) : row r = (rowElement r).val := by
  have h : row r = rowPerm r := by simp only [row, rowPerm, conjugator_eq]
  exact h.trans (rowPerm_eq r)

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover
