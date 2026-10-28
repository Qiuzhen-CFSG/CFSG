module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation.Coordinates
import Mathlib.Tactic.FinCases

/-!
# The three parameters of the inverter matrix

With y and u in the specified coordinates, `WY = YᵀW` and `WU = UW`
force W to have reverse-circulant rows and only three independent entries.
The proof reads the equations entry by entry; it does not enumerate matrices.
This is the linear part of the computation in Gorenstein, *Finite Groups*,
§16.6, pp.482–483. `ScalarRigidity` imposes the two power relations next.
-/

namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation

private abbrev Mat := Matrix (Fin 7) (Fin 7) (ZMod 11)
/-- The reverse-circulant matrix commuting with the marked cubic complement. -/
@[expose] public def inverterShape (a b c : ZMod 11) : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![a,b,c,c,a,c,a;
     b,c,c,a,c,a,a;
     c,c,a,c,a,a,b;
     c,a,c,a,a,b,c;
     a,c,a,a,b,c,c;
     c,a,a,b,c,c,a;
     a,a,b,c,c,a,c]
/-- The two normalizer relations leave exactly three scalar entries free. -/
public theorem inverter_shape_of_relations (W : Matrix (Fin 7) (Fin 7) (ZMod 11))
    (hY : W * sourceY = sourceY.transpose * W)
    (hU : W * normalU = normalU * W) : W = inverterShape (W 0 0) (W 0 1) (W 0 2) := by
  have hy10 : W 1 0 = W 0 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 1 1) hY
  have hy11 : W 1 1 = W 0 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 1 2) hY
  have hy12 : W 1 2 = W 0 3 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 1 3) hY
  have hy13 : W 1 3 = W 0 4 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 1 4) hY
  have hy14 : W 1 4 = W 0 5 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 1 5) hY
  have hy15 : W 1 5 = W 0 6 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 1 6) hY
  have hy16 : W 1 6 = W 0 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 1 0) hY
  have hy20 : W 2 0 = W 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 2 1) hY
  have hy21 : W 2 1 = W 1 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 2 2) hY
  have hy22 : W 2 2 = W 1 3 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 2 3) hY
  have hy23 : W 2 3 = W 1 4 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 2 4) hY
  have hy24 : W 2 4 = W 1 5 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 2 5) hY
  have hy25 : W 2 5 = W 1 6 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 2 6) hY
  have hy26 : W 2 6 = W 1 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 2 0) hY
  have hy30 : W 3 0 = W 2 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 3 1) hY
  have hy31 : W 3 1 = W 2 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 3 2) hY
  have hy32 : W 3 2 = W 2 3 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 3 3) hY
  have hy33 : W 3 3 = W 2 4 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 3 4) hY
  have hy34 : W 3 4 = W 2 5 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 3 5) hY
  have hy35 : W 3 5 = W 2 6 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 3 6) hY
  have hy36 : W 3 6 = W 2 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 3 0) hY
  have hy40 : W 4 0 = W 3 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 4 1) hY
  have hy41 : W 4 1 = W 3 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 4 2) hY
  have hy42 : W 4 2 = W 3 3 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 4 3) hY
  have hy43 : W 4 3 = W 3 4 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 4 4) hY
  have hy44 : W 4 4 = W 3 5 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 4 5) hY
  have hy45 : W 4 5 = W 3 6 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 4 6) hY
  have hy46 : W 4 6 = W 3 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 4 0) hY
  have hy50 : W 5 0 = W 4 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 5 1) hY
  have hy51 : W 5 1 = W 4 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 5 2) hY
  have hy52 : W 5 2 = W 4 3 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 5 3) hY
  have hy53 : W 5 3 = W 4 4 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 5 4) hY
  have hy54 : W 5 4 = W 4 5 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 5 5) hY
  have hy55 : W 5 5 = W 4 6 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 5 6) hY
  have hy56 : W 5 6 = W 4 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 5 0) hY
  have hy60 : W 6 0 = W 5 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 6 1) hY
  have hy61 : W 6 1 = W 5 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 6 2) hY
  have hy62 : W 6 2 = W 5 3 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 6 3) hY
  have hy63 : W 6 3 = W 5 4 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 6 4) hY
  have hy64 : W 6 4 = W 5 5 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 6 5) hY
  have hy65 : W 6 5 = W 5 6 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 6 6) hY
  have hy66 : W 6 6 = W 5 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, sourceY, Matrix.transpose_apply]
      using congrArg (fun A : Mat => A 6 0) hY
  have hu0 := congrArg (fun A : Mat => A 0 0) hU
  simp [Matrix.mul_apply, Fin.sum_univ_succ, normalU] at hu0
  have hu1 := congrArg (fun A : Mat => A 0 1) hU
  simp [Matrix.mul_apply, Fin.sum_univ_succ, normalU] at hu1
  have hu2 := congrArg (fun A : Mat => A 0 2) hU
  simp [Matrix.mul_apply, Fin.sum_univ_succ, normalU] at hu2
  have hu4 := congrArg (fun A : Mat => A 0 4) hU
  simp [Matrix.mul_apply, Fin.sum_univ_succ, normalU] at hu4
  have h03 : W 0 3 = W 0 2 := hu0.trans (hy20.trans hy11)
  have h05 : W 0 5 = W 0 2 := hu1.trans (hy21.trans (hy12.trans h03))
  have h04 : W 0 4 = W 0 0 := (hu2.trans (hy22.trans hy13)).symm
  have h06 : W 0 6 = W 0 0 := (hu4.trans (hy24.trans hy15)).symm.trans h04
  ext i j
  fin_cases i <;> fin_cases j
  · exact rfl
  · exact rfl
  · exact rfl
  · exact h03
  · exact h04
  · exact h05
  · exact h06
  · exact hy10
  · exact hy11
  · exact hy12.trans (h03)
  · exact hy13.trans (h04)
  · exact hy14.trans (h05)
  · exact hy15.trans (h06)
  · exact hy16
  · exact hy20.trans (hy11)
  · exact hy21.trans (hy12.trans (h03))
  · exact hy22.trans (hy13.trans (h04))
  · exact hy23.trans (hy14.trans (h05))
  · exact hy24.trans (hy15.trans (h06))
  · exact hy25.trans (hy16)
  · exact hy26.trans (hy10)
  · exact hy30.trans (hy21.trans (hy12.trans (h03)))
  · exact hy31.trans (hy22.trans (hy13.trans (h04)))
  · exact hy32.trans (hy23.trans (hy14.trans (h05)))
  · exact hy33.trans (hy24.trans (hy15.trans (h06)))
  · exact hy34.trans (hy25.trans (hy16))
  · exact hy35.trans (hy26.trans (hy10))
  · exact hy36.trans (hy20.trans (hy11))
  · exact hy40.trans (hy31.trans (hy22.trans (hy13.trans (h04))))
  · exact hy41.trans (hy32.trans (hy23.trans (hy14.trans (h05))))
  · exact hy42.trans (hy33.trans (hy24.trans (hy15.trans (h06))))
  · exact hy43.trans (hy34.trans (hy25.trans (hy16)))
  · exact hy44.trans (hy35.trans (hy26.trans (hy10)))
  · exact hy45.trans (hy36.trans (hy20.trans (hy11)))
  · exact hy46.trans (hy30.trans (hy21.trans (hy12.trans (h03))))
  · exact hy50.trans (hy41.trans (hy32.trans (hy23.trans (hy14.trans (h05)))))
  · exact hy51.trans (hy42.trans (hy33.trans (hy24.trans (hy15.trans (h06)))))
  · exact hy52.trans (hy43.trans (hy34.trans (hy25.trans (hy16))))
  · exact hy53.trans (hy44.trans (hy35.trans (hy26.trans (hy10))))
  · exact hy54.trans (hy45.trans (hy36.trans (hy20.trans (hy11))))
  · exact hy55.trans (hy46.trans (hy30.trans (hy21.trans (hy12.trans (h03)))))
  · exact hy56.trans (hy40.trans (hy31.trans (hy22.trans (hy13.trans (h04)))))
  · exact hy60.trans (hy51.trans (hy42.trans (hy33.trans (hy24.trans (hy15.trans (h06))))))
  · exact hy61.trans (hy52.trans (hy43.trans (hy34.trans (hy25.trans (hy16)))))
  · exact hy62.trans (hy53.trans (hy44.trans (hy35.trans (hy26.trans (hy10)))))
  · exact hy63.trans (hy54.trans (hy45.trans (hy36.trans (hy20.trans (hy11)))))
  · exact hy64.trans (hy55.trans (hy46.trans (hy30.trans (hy21.trans (hy12.trans (h03))))))
  · exact hy65.trans (hy56.trans (hy40.trans (hy31.trans (hy22.trans (hy13.trans (h04))))))
  · exact hy66.trans (hy50.trans (hy41.trans (hy32.trans (hy23.trans (hy14.trans (h05))))))

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation
