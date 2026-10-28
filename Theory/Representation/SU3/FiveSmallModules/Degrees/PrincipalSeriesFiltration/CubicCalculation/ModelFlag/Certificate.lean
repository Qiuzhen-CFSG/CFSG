module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Certificate.Checked
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Certificate.Agreement
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The uniform cubic matrix certificate

The checked coefficient matrices satisfy N = UV, LU = VR = I₂₁, and VU = 0.
These identities survive the constructed coefficient homomorphism into the
original field. They give N² = 0 and rank N = 21, while the independently
checked generator identities give equivariance. The final application supplies
the matrix premise of the actual principal-series flag consumer; its coordinate
comparison remains with that theorem's assembly owner.

Source motivation: Guralnick–Malle, Proposition 4.3, p.10. This proves only the
concrete arithmetic contract, not the independent group-coordinate comparison.
-/

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag
namespace Certificate
open Packed

private theorem rank_factor {K : Type*} [Field K] {n d : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin n) (Fin d) K)
    (C : Matrix (Fin d) (Fin n) K) (D : Matrix (Fin d) (Fin n) K)
    (E : Matrix (Fin n) (Fin d) K)
    (hbc : A = B * C) (hdb : D * B = 1) (hce : C * E = 1) :
    Module.finrank K (LinearMap.range A.toLin') = d := by
  change A.rank = d
  have h : D * A * E = 1 := by
    rw [hbc, ← Matrix.mul_assoc D B C, hdb, Matrix.one_mul, hce]
  have hlow : (1 : Matrix (Fin d) (Fin d) K).rank ≤ A.rank := by
    rw [← h]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have hupp : A.rank ≤ d := by
    rw [hbc]
    exact (Matrix.rank_mul_le_left _ _).trans B.rank_le_width
  exact Nat.le_antisymm hupp (by simpa using hlow)

private theorem coefficient_square : matrix 126 N * matrix 126 N = 0 := by
  rw [factorization]
  calc
    (matrix 21 U * matrix 126 V) * (matrix 21 U * matrix 126 V) =
        matrix 21 U * (matrix 126 V * matrix 21 U) * matrix 126 V := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [annihilation, Matrix.mul_zero, Matrix.zero_mul]

variable {K : Type*} [Field K] [CharP K 2] (z : K) (hz : z ^ 2 + z + 1 = 0)

private theorem specialize_nilpotent :
    (matrix 126 N).map (evaluate z hz) = nilpotentMatrix z hz := by
  rw [nilpotent_agreement]
  rfl

private theorem specialize_generator (a : Fin 2) :
    (matrix 126 (G a)).map (evaluate z hz) = generatorMatrix z hz a := by
  rw [generator_agreement]
  rfl

theorem nilpotent_square_zero : nilpotentMatrix z hz * nilpotentMatrix z hz = 0 := by
  have h := congrArg (fun A : Matrix (Fin 126) (Fin 126) CoefficientField =>
    A.map (evaluate z hz)) coefficient_square
  simpa only [Matrix.map_mul, specialize_nilpotent, Matrix.map_zero _ (map_zero _)] using h

theorem nilpotent_rank :
    Module.finrank K (LinearMap.range (nilpotentMatrix z hz).toLin') = 21 := by
  rw [← specialize_nilpotent]
  apply rank_factor _ ((matrix 21 U).map (evaluate z hz))
    ((matrix 126 V).map (evaluate z hz)) ((matrix 126 L).map (evaluate z hz))
    ((matrix 21 R).map (evaluate z hz))
  · exact (congrArg (fun A : Matrix (Fin 126) (Fin 126) CoefficientField =>
      A.map (evaluate z hz)) factorization).trans Matrix.map_mul
  · simpa only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] using
      congrArg (fun A : Matrix (Fin 21) (Fin 21) CoefficientField =>
        A.map (evaluate z hz)) left_inverse
  · simpa only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] using
      congrArg (fun A : Matrix (Fin 21) (Fin 21) CoefficientField =>
        A.map (evaluate z hz)) right_inverse

theorem nilpotent_commutes (a : Fin 2) :
    nilpotentMatrix z hz * generatorMatrix z hz a =
      generatorMatrix z hz a * nilpotentMatrix z hz := by
  have h := congrArg (fun A : Matrix (Fin 126) (Fin 126) CoefficientField =>
    A.map (evaluate z hz)) (commutation a)
  simpa only [Matrix.map_mul, specialize_nilpotent, specialize_generator] using h

end Certificate

universe v
/-- All three concrete matrix obligations, over the original coefficient field. -/
theorem matrix_relations : MatrixRelations.{v} where
  square_zero K _ _ z hz := Certificate.nilpotent_square_zero (K := K) z hz
  rank K _ _ z hz := Certificate.nilpotent_rank (K := K) z hz
  commutes K _ _ z hz a := Certificate.nilpotent_commutes (K := K) z hz a

/-- The actual flag consumer now needs only its independent coordinate comparison. -/
noncomputable def model_flags_of_coordinates (hc : ModelCoordinates.{v}) : ModelFlags.{v} :=
  model_flags_of_coordinates_and_relations hc matrix_relations

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag
