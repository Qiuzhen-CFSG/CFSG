module
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.DistanceMatrices
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.Spectral

/-!
# Feit--Higman square constraints for finite even polygons

The actual distance matrices give the rational quadratic trace argument.
Thickness ensures its trace is nonzero. Source: Feit--Higman (1964),
Theorems 1--2, as used in Fong--Seitz I (1J).
-/

public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.PolygonParameters
open SimpleGraph.PolygonParameters
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {s t : ℕ}

theorem hexagon_square (D : Datum G 6 s t) (hs : 1<s) (ht : 1<t)
    (hp : ∃ v, D.color v=0) : IsSquare (s*t) := by
  classical
  let : Nonempty D.Point := ⟨⟨hp.choose,hp.choose_spec⟩⟩
  apply hexagon_square_of_recurrence
    (Matrix.toLin' (D.distanceMatrix 1)) (Matrix.toLin' (D.distanceMatrix 2))
    (Matrix.toLin' (D.distanceMatrix 3)) s t (Fintype.card D.Point)
    hs ht Fintype.card_pos
  · have h := congrArg Matrix.toLin' D.hexagon_recurrence_1
    simpa only [Matrix.toLin'_mul, map_add, map_smul,
      D.distanceMatrix_zero, Matrix.toLin'_one, Module.End.mul_eq_comp,
      Module.End.one_eq_id] using h
  · have h := congrArg Matrix.toLin' D.hexagon_recurrence_2
    simpa only [Matrix.toLin'_mul, map_add, map_smul,
      Module.End.mul_eq_comp] using h
  · have h := congrArg Matrix.toLin' D.hexagon_recurrence_3
    simpa only [Matrix.toLin'_mul, map_add, map_smul,
      Module.End.mul_eq_comp] using h
  · rw [LinearMap.trace_one, Module.finrank_fintype_fun_eq_card]
  · rw [Matrix.trace_toLin'_eq, D.trace_distanceMatrix 1 (by decide)]
  · rw [Matrix.trace_toLin'_eq, D.trace_distanceMatrix 2 (by decide)]
  · rw [Matrix.trace_toLin'_eq, D.trace_distanceMatrix 3 (by decide)]

theorem octagon_square (D : Datum G 8 s t) (hs : 1<s) (ht : 1<t)
    (hp : ∃ v, D.color v=0) : IsSquare (2*s*t) := by
  classical
  let : Nonempty D.Point := ⟨⟨hp.choose,hp.choose_spec⟩⟩
  apply octagon_square_of_recurrence
    (Matrix.toLin' (D.distanceMatrix 1)) (Matrix.toLin' (D.distanceMatrix 2))
    (Matrix.toLin' (D.distanceMatrix 3)) (Matrix.toLin' (D.distanceMatrix 4))
    s t (Fintype.card D.Point) hs ht Fintype.card_pos
  · have h := congrArg Matrix.toLin' D.octagon_recurrence_1
    simpa only [Matrix.toLin'_mul, map_add, map_smul,
      D.distanceMatrix_zero, Matrix.toLin'_one, Module.End.mul_eq_comp,
      Module.End.one_eq_id] using h
  · have h := congrArg Matrix.toLin' D.octagon_recurrence_2
    simpa only [Matrix.toLin'_mul, map_add, map_smul,
      Module.End.mul_eq_comp] using h
  · have h := congrArg Matrix.toLin' D.octagon_recurrence_3
    simpa only [Matrix.toLin'_mul, map_add, map_smul,
      Module.End.mul_eq_comp] using h
  · have h := congrArg Matrix.toLin' D.octagon_recurrence_4
    simpa only [Matrix.toLin'_mul, map_add, map_smul,
      Module.End.mul_eq_comp] using h
  · rw [LinearMap.trace_one, Module.finrank_fintype_fun_eq_card]
  · rw [Matrix.trace_toLin'_eq, D.trace_distanceMatrix 1 (by decide)]
  · rw [Matrix.trace_toLin'_eq, D.trace_distanceMatrix 2 (by decide)]
  · rw [Matrix.trace_toLin'_eq, D.trace_distanceMatrix 3 (by decide)]
  · rw [Matrix.trace_toLin'_eq, D.trace_distanceMatrix 4 (by decide)]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.PolygonParameters
