module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.Data

/-!
# Reconstruction from explicit linear and quadratic column equations

Twenty-two independent columns and their dual rows give coordinates for a
candidate quadratic family in the published 112-dimensional column module.
A column satisfying the reconstruction, normalization, and nine quadratic
equations is the parametrization at its own twelve free coordinates. These
coordinates determine a Boolean mask. The dual-pairing matrix and the constant
column (a - 1)e₀ are checked by Lean's kernel.

The equations themselves make no assertion about the full homology kernel,
and the parametrization is not yet identified with the specified local words.
Those are independent obligations in OrbitCover. Source motivation: GLS3,
Table 5.3i, printed p.270. See source/README.md for provenance, conventions,
and the distinction between the checked coordinate identities and the
untrusted numerical word exploration.
-/

@[expose] public section
open scoped Matrix

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

/-- Decode a binary column in the original ATLAS coordinate order. -/
def binaryColumn (n : ℕ) : NaturalModule :=
  fun i => if n.testBit i.val then 1 else 0

/-- The constant column, twelve linear columns, and nine quadratic columns. -/
def basisVector (i : Fin 22) : NaturalModule := binaryColumn (basisColumns.get i)

/-- Extract 22 coefficients by the explicitly certified dual rows. -/
def coordinates (v : NaturalModule) (i : Fin 22) : ZMod 2 :=
  binaryColumn (dualRows.get i) ⬝ᵥ v

/-- Form the column with the given 22 coefficients. -/
def synthesize (x : Fin 22 → ZMod 2) : NaturalModule := ∑ i, x i • basisVector i

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem coordinate_pairing : ∀ i j : Fin 22,
    binaryColumn (dualRows.get i) ⬝ᵥ basisVector j = if i = j then 1 else 0 := by
  decide +kernel

theorem coordinates_synthesize (x : Fin 22 → ZMod 2) :
    coordinates (synthesize x) = x := by
  funext i
  dsimp only [coordinates, synthesize]
  rw [dotProduct_sum]
  simp only [dotProduct_smul, coordinate_pairing]
  simp

/-- Positions 1 through 12 in the 22-coordinate chart. -/
def freeIndex (i : Fin 12) : Fin 22 := ⟨i.val + 1, by omega⟩
/-- Positions 13 through 21 in the 22-coordinate chart. -/
def quadraticIndex (i : Fin 9) : Fin 22 := ⟨i.val + 13, by omega⟩

/-- The twelve free parameters extracted from any column. -/
def freeCoordinates (v : NaturalModule) (i : Fin 12) : ZMod 2 :=
  coordinates v (freeIndex i)

/-- One of nine explicit homogeneous quadratic forms in twelve variables. -/
def quadraticCoordinate (i : Fin 9) (x : Fin 12 → ZMod 2) : ZMod 2 :=
  ((quadraticTerms.get i).map (fun p => x p.1 * x p.2)).sum

/-- Constant, free, and quadratic coordinates of a parameter value. -/
def parameterCoordinates (x : Fin 12 → ZMod 2) (i : Fin 22) : ZMod 2 :=
  if h0 : i.val = 0 then 1
  else if h1 : i.val < 13 then x ⟨i.val - 1, by omega⟩
  else quadraticCoordinate ⟨i.val - 13, by omega⟩ x

theorem parameterCoordinates_zero (x : Fin 12 → ZMod 2) :
    parameterCoordinates x 0 = 1 := rfl

theorem parameterCoordinates_free (x : Fin 12 → ZMod 2) (i : Fin 12) :
    parameterCoordinates x (freeIndex i) = x i := by
  simp only [parameterCoordinates, freeIndex, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, ↓reduceDIte, Nat.add_sub_cancel]
  split
  · rfl
  · omega

theorem parameterCoordinates_quadratic (x : Fin 12 → ZMod 2) (i : Fin 9) :
    parameterCoordinates x (quadraticIndex i) = quadraticCoordinate i x := by
  simp only [parameterCoordinates, quadraticIndex,
    show ¬ i.val + 13 = 0 by omega, ↓reduceDIte,
    show ¬ i.val + 13 < 13 by omega, Nat.add_sub_cancel]

/-- The explicit degree-two parametrization, without any group-membership assertion. -/
def quadraticVector (x : Fin 12 → ZMod 2) : NaturalModule :=
  synthesize (parameterCoordinates x)

theorem freeCoordinates_quadraticVector (x : Fin 12 → ZMod 2) :
    freeCoordinates (quadraticVector x) = x := by
  funext i
  change coordinates (synthesize (parameterCoordinates x)) (freeIndex i) = x i
  rw [coordinates_synthesize, parameterCoordinates_free]

/-- Linear reconstruction, normalization, and nine quadratic equations. -/
def SatisfiesEquations (v : NaturalModule) : Prop :=
  v = synthesize (coordinates v) ∧
    coordinates v 0 = 1 ∧
      ∀ i : Fin 9, coordinates v (quadraticIndex i) =
        quadraticCoordinate i (freeCoordinates v)

theorem coordinates_eq_parameters {v : NaturalModule} (hv : SatisfiesEquations v) :
    coordinates v = parameterCoordinates (freeCoordinates v) := by
  funext i
  by_cases h0 : i.val = 0
  · have hi : i = 0 := Fin.ext h0
    subst i
    rw [parameterCoordinates_zero]
    exact hv.2.1
  · by_cases h1 : i.val < 13
    · let j : Fin 12 := ⟨i.val - 1, by omega⟩
      have hi : i = freeIndex j := Fin.ext (by dsimp [freeIndex, j]; omega)
      rw [hi, parameterCoordinates_free]
      rfl
    · let j : Fin 9 := ⟨i.val - 13, by omega⟩
      have hi : i = quadraticIndex j := Fin.ext (by dsimp [quadraticIndex, j]; omega)
      rw [hi, parameterCoordinates_quadratic]
      exact hv.2.2 j

theorem eq_quadraticVector_of_equations {v : NaturalModule} (hv : SatisfiesEquations v) :
    v = quadraticVector (freeCoordinates v) := by
  rw [quadraticVector, ← coordinates_eq_parameters hv]
  exact hv.1

theorem quadraticVector_satisfies (x : Fin 12 → ZMod 2) :
    SatisfiesEquations (quadraticVector x) := by
  refine ⟨?_, ?_, ?_⟩
  · change synthesize (parameterCoordinates x) =
      synthesize (coordinates (synthesize (parameterCoordinates x)))
    rw [coordinates_synthesize]
  · change coordinates (synthesize (parameterCoordinates x)) 0 = 1
    rw [coordinates_synthesize, parameterCoordinates_zero]
  · intro i
    rw [freeCoordinates_quadraticVector]
    change coordinates (synthesize (parameterCoordinates x)) (quadraticIndex i) = _
    rw [coordinates_synthesize, parameterCoordinates_quadratic]

/-- Turn the twelve Boolean choices into binary-field parameters. -/
def maskCoordinates (m : OrbitMask) : Fin 12 → ZMod 2 :=
  fun i => if m i then 1 else 0

/-- Recover the only possible mask from the twelve extracted parameters. -/
def recoveredMask (v : NaturalModule) : OrbitMask :=
  fun i => decide (freeCoordinates v i = 1)

theorem maskCoordinates_recoveredMask (v : NaturalModule) :
    maskCoordinates (recoveredMask v) = freeCoordinates v := by
  funext i
  have htwo : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases htwo (freeCoordinates v i) with h | h <;>
    simp [maskCoordinates, recoveredMask, h]

theorem eq_quadraticVector_recoveredMask {v : NaturalModule} (hv : SatisfiesEquations v) :
    v = quadraticVector (maskCoordinates (recoveredMask v)) := by
  rw [maskCoordinates_recoveredMask]
  exact eq_quadraticVector_of_equations hv

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem basisVector_zero : basisVector 0 = (baseVector : NaturalModule) := by
  change basisVector 0 = displacement (Pi.single 0 1)
  rw [displacement_apply]
  decide +kernel

theorem quadraticCoordinate_zero (i : Fin 9) : quadraticCoordinate i 0 = 0 := by
  simp [quadraticCoordinate]

theorem quadraticVector_zero : quadraticVector 0 = (baseVector : NaturalModule) := by
  have h : parameterCoordinates 0 = Pi.single 0 (1 : ZMod 2) := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp only [parameterCoordinates_zero, Pi.single_eq_same]
    · have hi' : i.val ≠ 0 := fun h => hi (Fin.ext h)
      simp only [parameterCoordinates, hi', ↓reduceDIte, Pi.single_eq_of_ne hi]
      split
      · rfl
      · exact quadraticCoordinate_zero _
  rw [quadraticVector, h, synthesize]
  simp [basisVector_zero]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
