module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Loop

/-!
# The Parker permutations on triples

The permutations below are the three loop translations and the even/odd
standard-automorphism formulas of Aschbacher, *Sporadic Groups*, Section 14,
pp. 58–59. They act on all triples from the loop with an adjoined zero.
The coordinate axes are retained for the signed modules of Section 27.
Function composition uses Lean's convention: `(g * h) x = g (h x)`;
the displayed formulas specify the maps independently of this convention.
-/

@[expose] public section

noncomputable section

open Atlas.Fischer Atlas.Codes

namespace Sporadic.Monster.Construction.TrialitySpin

/-- The map `(a,b,c) ↦ (d⁻¹ a d⁻¹, d b, c d)` of Section 14. -/
def psi1 (d : ParkerLoop) : Equiv.Perm Triple :=
  Equiv.prodCongr ((leftZero (loopInverse d)).trans (rightZero (loopInverse d)))
    (Equiv.prodCongr (leftZero d) (rightZero d))

/-- The map `(a,b,c) ↦ (a d, d⁻¹ b d⁻¹, d c)` of Section 14. -/
def psi2 (d : ParkerLoop) : Equiv.Perm Triple :=
  Equiv.prodCongr (rightZero d)
    (Equiv.prodCongr ((leftZero (loopInverse d)).trans (rightZero (loopInverse d)))
      (leftZero d))

/-- The map `(a,b,c) ↦ (d a, b d, d⁻¹ c d⁻¹)` of Section 14. -/
def psi3 (d : ParkerLoop) : Equiv.Perm Triple :=
  Equiv.prodCongr (leftZero d)
    (Equiv.prodCongr (rightZero d)
      ((leftZero (loopInverse d)).trans (rightZero (loopInverse d))))

@[simp] theorem psi1_apply (d : ParkerLoop) (a b c : LoopZero) :
    psi1 d (a, b, c) =
      (rightZero (loopInverse d) (leftZero (loopInverse d) a), leftZero d b, rightZero d c) := rfl

@[simp] theorem psi2_apply (d : ParkerLoop) (a b c : LoopZero) :
    psi2 d (a, b, c) =
      (rightZero d a, rightZero (loopInverse d) (leftZero (loopInverse d) b), leftZero d c) := rfl

@[simp] theorem psi3_apply (d : ParkerLoop) (a b c : LoopZero) :
    psi3 d (a, b, c) =
      (leftZero d a, rightZero d b, rightZero (loopInverse d) (leftZero (loopInverse d) c)) := rfl

/-- Simultaneous application of a loop permutation, fixing the adjoined zero. -/
def diagonal (e : Equiv.Perm ParkerLoop) : Equiv.Perm Triple :=
  Equiv.prodCongr (Equiv.optionCongr e)
    (Equiv.prodCongr (Equiv.optionCongr e) (Equiv.optionCongr e))

/-- Inversion on every coordinate, followed by interchange of axes 2 and 3. -/
def flip1 : Equiv.Perm Triple where
  toFun t := (inverseZero t.1, inverseZero t.2.2, inverseZero t.2.1)
  invFun t := (inverseZero t.1, inverseZero t.2.2, inverseZero t.2.1)
  left_inv := by rintro ⟨a, b, c⟩; simp
  right_inv := by rintro ⟨a, b, c⟩; simp

/-- Inversion on every coordinate, followed by interchange of axes 1 and 3. -/
def flip2 : Equiv.Perm Triple where
  toFun t := (inverseZero t.2.2, inverseZero t.2.1, inverseZero t.1)
  invFun t := (inverseZero t.2.2, inverseZero t.2.1, inverseZero t.1)
  left_inv := by rintro ⟨a, b, c⟩; simp
  right_inv := by rintro ⟨a, b, c⟩; simp

/-- Inversion on every coordinate, followed by interchange of axes 1 and 2. -/
def flip3 : Equiv.Perm Triple where
  toFun t := (inverseZero t.2.1, inverseZero t.1, inverseZero t.2.2)
  invFun t := (inverseZero t.2.1, inverseZero t.1, inverseZero t.2.2)
  left_inv := by rintro ⟨a, b, c⟩; simp
  right_inv := by rintro ⟨a, b, c⟩; simp

/-- The parity-dependent first standard-automorphism permutation. -/
def psiAut1 (e : Equiv.Perm ParkerLoop) : Equiv.Perm Triple :=
  if e parkerOmega = parkerOmega then diagonal e else flip1.trans (diagonal e)

/-- The parity-dependent second standard-automorphism permutation. -/
def psiAut2 (e : Equiv.Perm ParkerLoop) : Equiv.Perm Triple :=
  if e parkerOmega = parkerOmega then diagonal e else flip2.trans (diagonal e)

/-- The parity-dependent third standard-automorphism permutation. -/
def psiAut3 (e : Equiv.Perm ParkerLoop) : Equiv.Perm Triple :=
  if e parkerOmega = parkerOmega then diagonal e else flip3.trans (diagonal e)

/-- A cyclic coordinate permutation, used to compare the three formulas. -/
def cycle : Equiv.Perm Triple where
  toFun t := (t.2.2, t.1, t.2.1)
  invFun t := (t.2.1, t.2.2, t.1)
  left_inv _ := rfl
  right_inv _ := rfl

theorem cycle_cube : cycle ^ 3 = 1 := by
  apply Equiv.ext
  rintro ⟨a, b, c⟩
  rfl

/-- The three coordinate-axis parametrizations. -/
def axis1 (d : ParkerLoop) : Triple := (some d, none, none)
def axis2 (d : ParkerLoop) : Triple := (none, some d, none)
def axis3 (d : ParkerLoop) : Triple := (none, none, some d)

def A1 : Set Triple := Set.range axis1
def A2 : Set Triple := Set.range axis2
def A3 : Set Triple := Set.range axis3
/-- The two axes used for the first spin module. -/
def A : Set Triple := A2 ∪ A3

@[simp] theorem psi1_axis2 (d b : ParkerLoop) :
    psi1 d (axis2 b) = axis2 (parkerLoopMultiply d b) := rfl

@[simp] theorem psi1_axis3 (d b : ParkerLoop) :
    psi1 d (axis3 b) = axis3 (parkerLoopMultiply b d) := rfl

@[simp] theorem psi2_axis1 (d b : ParkerLoop) :
    psi2 d (axis1 b) = axis1 (parkerLoopMultiply b d) := rfl

@[simp] theorem psi3_axis1 (d b : ParkerLoop) :
    psi3 d (axis1 b) = axis1 (parkerLoopMultiply d b) := rfl

/-- The three distinguished sign involutions. -/
def z1 : Equiv.Perm Triple := psi1 loopPi
def z2 : Equiv.Perm Triple := psi2 loopPi
def z3 : Equiv.Perm Triple := psi3 loopPi

@[simp] theorem z1_apply (a b c : LoopZero) :
    z1 (a, b, c) = (a, signZero b, signZero c) := by
  simp [z1]

@[simp] theorem z2_apply (a b c : LoopZero) :
    z2 (a, b, c) = (signZero a, b, signZero c) := by
  simp [z2]

@[simp] theorem z3_apply (a b c : LoopZero) :
    z3 (a, b, c) = (signZero a, signZero b, c) := by
  simp [z3]

theorem z1_sq : z1 ^ 2 = 1 := by
  ext ⟨a, b, c⟩ : 1
  simp [pow_two, Equiv.Perm.mul_apply]

theorem z2_sq : z2 ^ 2 = 1 := by
  ext ⟨a, b, c⟩ : 1
  simp [pow_two, Equiv.Perm.mul_apply]

theorem z3_sq : z3 ^ 2 = 1 := by
  ext ⟨a, b, c⟩ : 1
  simp [pow_two, Equiv.Perm.mul_apply]

theorem z1_z2_z3 : z1 * z2 * z3 = 1 := by
  ext ⟨a, b, c⟩ : 1
  simp [Equiv.Perm.mul_apply]

end Sporadic.Monster.Construction.TrialitySpin
