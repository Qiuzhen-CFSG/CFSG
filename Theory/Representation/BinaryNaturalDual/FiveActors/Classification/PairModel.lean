module

public import Theory.Representation.BinaryNaturalDual.FiveActors.Basic

/-!
# A marked nonquadratic commuting involution pair

On the basis `(v, xv, yv, xyv, w)`, the two operators are `1+x` and
`1+y`, with `x²=y²=0` and `xy=yx`. They act regularly on the first four
dimensions and fix the fifth. Their common centralizer is the concrete
subgroup needed to exclude nonquadratic elementary subgroups of rank five.

Only the model and its elementary identities are proved here. Conjugacy
of arbitrary nonquadratic pairs and the common-centralizer rank bound are
separate results, both required for the classification assembly.
Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
H.9.2(3), printed pp.390–391; this is an alternative linear-algebra route.
-/

@[expose] public section

namespace BinaryNaturalDual.FiveActors.Classification

def regularS : G where
  toFun x := ![x 0, x 1 + x 0, x 2, x 3 + x 2, x 4]
  invFun x := ![x 0, x 1 + x 0, x 2, x 3 + x 2, x 4]
  left_inv x := by ext i; fin_cases i <;> simp [add_assoc, ← two_mul, show (2 : ZMod 2) = 0 from rfl]
  right_inv x := by ext i; fin_cases i <;> simp [add_assoc, ← two_mul, show (2 : ZMod 2) = 0 from rfl]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp [mul_add]

def regularT : G where
  toFun x := ![x 0, x 1, x 2 + x 0, x 3 + x 1, x 4]
  invFun x := ![x 0, x 1, x 2 + x 0, x 3 + x 1, x 4]
  left_inv x := by ext i; fin_cases i <;> simp [add_assoc, ← two_mul, show (2 : ZMod 2) = 0 from rfl]
  right_inv x := by ext i; fin_cases i <;> simp [add_assoc, ← two_mul, show (2 : ZMod 2) = 0 from rfl]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp [mul_add]

def regularCentralizer : Subgroup G := Subgroup.centralizer {regularS, regularT}

theorem regularS_sq : regularS ^ 2 = 1 := by
  ext x i
  change (regularS (regularS x)) i = x i
  exact congrFun (regularS.left_inv x) i

theorem regularT_sq : regularT ^ 2 = 1 := by
  ext x i
  change (regularT (regularT x)) i = x i
  exact congrFun (regularT.left_inv x) i

theorem regular_commute : regularS * regularT = regularT * regularS := by
  ext x i
  fin_cases i <;> simp [regularS, regularT, LinearEquiv.mul_apply]; ring

theorem regular_nonquadratic :
    ∃ x : X, regularS (regularT x - x) ≠ regularT x - x := by
  refine ⟨![1, 0, 0, 0, 0], ?_⟩
  decide

end BinaryNaturalDual.FiveActors.Classification
