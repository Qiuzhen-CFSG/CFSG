module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison.Transport
public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison.Matrices
public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison.PointCoordinates

/-!
# Comparison of the saved M23 matrices with native induction

The original right-coset action is evaluated at the inverses of the certified
saved transversal. Applying the same ten-dimensional coordinates in every
block and flattening gives the full generator equations. Native generation
and every saved column identity are proved in the imported modules.

The literal M22 cocode quotient is identified with the displayed ten
coordinates by `NativeComparison.nativePointCoordinates`. Substituting this
proved local comparison gives `nativeGeneratorCoordinates` without any
additional premise. Matrix simplicity remains independent of this comparison.

Source application: Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, M23 paragraph, journal p.366/manuscript p.16.
-/

namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration
namespace NativeComparison
@[expose] public noncomputable section

/-- Flatten the ordered 23 blocks of ten coordinates. -/
def flatten : (Fin 23 → Fin 10 → ZMod 2) ≃ₗ[ZMod 2] Space where
  toFun v x := v ((finProdFinEquiv (m := 23) (n := 10)).symm x).1 ((finProdFinEquiv (m := 23) (n := 10)).symm x).2
  invFun v i y := v (finProdFinEquiv (i,y))
  left_inv v := by
    funext i y
    dsimp only
    rw [_root_.Equiv.symm_apply_apply]
  right_inv v := by
    funext x
    dsimp only
    rw [_root_.Equiv.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flatten_apply (v : Fin 23 → Fin 10 → ZMod 2) (i : Fin 23) (y : Fin 10) :
    flatten v (finProdFinEquiv (i,y)) = v i y := by
  change v (finProdFinEquiv.symm (finProdFinEquiv (i,y))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i,y))).2 = _
  rw [_root_.Equiv.symm_apply_apply]

/-- Apply the same native cocode coordinates in each of the 23 blocks. -/
def pointwiseCoordinates (C : PointCoordinates) :
    (Fin 23 → Models.Space false) ≃ₗ[ZMod 2] (Fin 23 → Fin 10 → ZMod 2) where
  toFun v i := C.equiv (v i)
  invFun v i := C.equiv.symm (v i)
  left_inv v := by
    funext i
    exact C.equiv.symm_apply_apply (v i)
  right_inv v := by
    funext i
    exact C.equiv.apply_symm_apply (v i)
  map_add' u v := by
    funext i
    exact C.equiv.map_add (u i) (v i)
  map_smul' c v := by
    funext i
    exact C.equiv.map_smul c (v i)

/-- Only the literal ten-dimensional point-module comparison is an input. -/
def coordinatesOfPoint (C : PointCoordinates) : Coordinates.Space false ≃ₗ[ZMod 2] Space :=
  (evaluationEquiv.trans (pointwiseCoordinates C)).trans flatten

theorem coordinatesOfPoint_apply (C : PointCoordinates)
    (v : Coordinates.Space false) (i : Fin 23) (y : Fin 10) :
    coordinatesOfPoint C v (finProdFinEquiv (i,y)) = C.equiv (evaluationEquiv v i) y :=
  flatten_apply (fun j => C.equiv (evaluationEquiv v j)) i y

/-- Every full saved generator equation follows from the local quotient equation. -/
theorem coordinatesOfPoint_generator (C : PointCoordinates) (k : Fin 2)
    (v : Coordinates.Space false) :
    coordinatesOfPoint C (canonicalCocodeAction (actor k) v) =
      (generatorMatrix k).mulVec (coordinatesOfPoint C v) := by
  funext x
  obtain ⟨⟨j,y⟩, rfl⟩ := (finProdFinEquiv (m := 23) (n := 10)).surjective x
  obtain ⟨i, rfl⟩ := (blockPerm k).surjective j
  rw [coordinatesOfPoint_apply, evaluation_generator, C.intertwines, saved_mulVec]
  exact congrArg (fun w : Fin 10 → ZMod 2 => (pointMatrix (correction k i)).mulVec w y)
    (funext fun z => (coordinatesOfPoint_apply C v i z).symm)

end
end NativeComparison

/-- Native induction comparison assembled from any local cocode coordinates.
The native generation and all 460 saved columns are already discharged. -/
@[expose] public noncomputable def generatorCoordinatesOfPointCoordinates (C : NativeComparison.PointCoordinates) :
    GeneratorCoordinates where
  equiv := NativeComparison.coordinatesOfPoint C
  intertwines := NativeComparison.coordinatesOfPoint_generator C
  generates := NativeComparison.native_generates

/-- The actual native M23 cocode induction in the 230 saved coordinates.
The point quotient, inverse-transversal action, both generator matrices and
generation are all proved; this construction takes no certificate premise. -/
@[expose] public noncomputable def nativeGeneratorCoordinates : GeneratorCoordinates :=
  generatorCoordinatesOfPointCoordinates NativeComparison.nativePointCoordinates

end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration
