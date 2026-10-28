module
public import Theory.Representation.OrthogonalFourPlusMatrix.PrimeFieldTwo.Stabilizers

/-!
# The source tensor factor's orbit plane

The left cubic on determinant matrices has no nonzero fixed vector. Its
three images of a singular vector are precisely the three nonzero vectors
of a totally singular plane. This uses the literal determinant action of
G.2.6, so it retains the chosen Y₁ factor in source 15.3.56.
-/

@[expose] public noncomputable section
open Matrix
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.MatrixOrbit
open ClassicalOrthogonal.FourPlusMatrix
abbrev M := Mat (F := ZMod 2)

def cubic : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  ⟨!![0, 1; 1, 1], by decide⟩

def leftCubic : PairSL (F := ZMod 2) := (cubic, 1)

theorem cubic_cube : cubic ^ 3 = 1 := by decide +kernel

theorem cubic_second (X : M) : matrixAction (leftCubic ^ 2) X =
    X + matrixAction leftCubic X := by
  exact (show ∀ X : M, matrixAction (leftCubic ^ 2) X =
    X + matrixAction leftCubic X by decide +kernel) X

theorem cubic_moves (X : M) (hX : X ≠ 0) : matrixAction leftCubic X ≠ X := by
  exact (show ∀ X : M, X ≠ 0 → matrixAction leftCubic X ≠ X by decide +kernel) X hX

/-- The two indicated coordinates are linearly independent for every nonzero point. -/
theorem orbit_coordinates_injective (X : M) (hX : X ≠ 0) :
    Function.Injective (fun a : Fin 2 → ZMod 2 =>
      a 0 • X + a 1 • matrixAction leftCubic X) := by
  exact (show ∀ X : M, X ≠ 0 →
    Function.Injective (fun a : Fin 2 → ZMod 2 =>
      a 0 • X + a 1 • matrixAction leftCubic X) by decide +kernel) X hX

/-- The orbit plane is singular on the actual determinant form. -/
theorem orbit_totally_singular (X : M) (hX : X.det = 0)
    (a b : ZMod 2) : determinantForm (a • X + b • matrixAction leftCubic X) = 0 := by
  rw [determinantForm_apply]
  exact (show ∀ (X : M) (a b : ZMod 2), X.det = 0 →
    (a • X + b • matrixAction leftCubic X).det = 0 by decide +kernel) X a b hX

/-- A pair of the actual conjugate point stabilizers contains the left cubic.
The witness is chosen inside the original stabilizer, with no change of point. -/
theorem cubic_word (X : M) (hX : X ≠ 0) (hs : X.det = 0) :
    ∃ u : PairSL (F := ZMod 2), matrixAction u X = X ∧
      (u * (leftCubic⁻¹ * u * leftCubic)) ^ 2 = leftCubic := by
  exact (show ∀ X : M, X ≠ 0 → X.det = 0 →
    ∃ u : PairSL (F := ZMod 2), matrixAction u X = X ∧
      (u * (leftCubic⁻¹ * u * leftCubic)) ^ 2 = leftCubic by decide +kernel) X hX hs

/-- The kernel of the action on the orbit plane is precisely the remaining
right-hand involution, expressed as an equality in the literal model. -/
theorem orbit_plane_kernel (X : M) (hX : X ≠ 0)
    (a : PairSL (F := ZMod 2))
    (hr : matrixAction (1, a.2) X = X) :
    (matrixAction a X = X ∧
      matrixAction a (matrixAction leftCubic X) = matrixAction leftCubic X) ↔ a.1 = 1 := by
  exact (show ∀ X : M, X ≠ 0 → ∀ a : PairSL (F := ZMod 2),
    matrixAction (1, a.2) X = X →
    ((matrixAction a X = X ∧
      matrixAction a (matrixAction leftCubic X) = matrixAction leftCubic X) ↔ a.1 = 1)
      by decide +kernel) X hX a hr

/-- Every element of the rank-one model is a cubic power times an original
point stabilizer element. This bounds the local model by twelve elements. -/
theorem rank_one_words (X : M) (hX : X ≠ 0) (hs : X.det = 0)
    (a : PairSL (F := ZMod 2)) (hr : matrixAction (1, a.2) X = X) :
    ∃ k : Fin 3, ∃ u : PairSL (F := ZMod 2),
      matrixAction u X = X ∧ a = leftCubic ^ k.val * u := by
  exact (show ∀ X : M, X ≠ 0 → X.det = 0 → ∀ a : PairSL (F := ZMod 2),
    matrixAction (1, a.2) X = X →
    ∃ k : Fin 3, ∃ u : PairSL (F := ZMod 2),
      matrixAction u X = X ∧ a = leftCubic ^ k.val * u by decide +kernel) X hX hs a hr

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.MatrixOrbit
