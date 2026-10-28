module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison.Generators

/-!
# Explicit native transversal and point-coordinate data

The words specify genuine M23 elements. Their point tables and the induced
block permutation retain the ordering of the original GAP right transversal.
The projection masks express each star vector e_i + e_24 modulo Golay and
e_9 + e_24 in the ordered basis e_14 + e_24, ..., e_23 + e_24.
These data alone assert no linear equivalence or action comparison.

Source: `InducedHeads/source/native-candidate.json`, and the diagnostic
`CocodeFiltration/source/check-induction.py`. See `source/README.md`.
-/

@[expose] public noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.LargeInvolutionGeneration
namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison

/-- Native generator words, with GAP multiplication order reversed. -/
def transversalWord : Fin 23 → List (Fin 4) :=
![[],
  [3],
  [2, 3],
  [1, 1, 1, 2, 3],
  [2, 3, 2, 3],
  [1, 1, 2, 3],
  [1, 1, 1, 2, 3, 2, 3],
  [2, 3, 3, 2, 3],
  [1, 0, 3],
  [1, 1, 2, 3, 2, 3],
  [3, 2, 3, 3, 2, 3],
  [2, 3, 3, 2, 3, 2, 3],
  [1, 2, 3, 2, 3],
  [3, 3, 2, 3, 3, 2, 3],
  [3, 0, 1, 1, 0, 1, 1, 1, 2, 3],
  [0, 1, 0, 3, 0, 3],
  [2, 3, 3, 2, 3, 3, 2, 3],
  [3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 1],
  [1, 1, 2, 3, 3, 2, 3, 2, 3],
  [3, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 2, 3],
  [0, 1, 0, 1, 1, 0, 1, 1, 1, 2, 3],
  [3, 0, 1, 0, 1, 1, 0, 1, 1, 1, 2, 3],
  [2, 3, 2, 1, 2, 3, 3, 2, 3, 2, 3]]

/-- The saved transversal as actual members of the native group. -/
def transversal (i : Fin 23) : M23 := evalWord letter (transversalWord i)

/-- Point tables use native labels: Atlas 23 is zero. -/
def transversalPoint : Fin 23 → Fin 23 → Fin 23 :=
![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22],
  ![1, 7, 19, 3, 13, 2, 21, 11, 10, 18, 8, 0, 15, 16, 14, 6, 17, 4, 9, 20, 5, 12, 22],
  ![1, 16, 19, 10, 2, 13, 20, 11, 3, 4, 6, 14, 15, 7, 0, 8, 17, 18, 9, 21, 22, 12, 5],
  ![7, 17, 20, 8, 19, 16, 5, 0, 3, 13, 21, 14, 6, 11, 1, 10, 4, 9, 18, 12, 22, 15, 2],
  ![16, 17, 21, 6, 19, 7, 22, 14, 10, 2, 20, 0, 8, 11, 1, 3, 18, 9, 4, 12, 5, 15, 13],
  ![11, 4, 5, 10, 20, 17, 2, 1, 3, 16, 12, 14, 21, 0, 7, 8, 13, 18, 9, 15, 22, 6, 19],
  ![17, 4, 12, 21, 20, 11, 22, 14, 8, 19, 5, 1, 10, 0, 7, 3, 9, 18, 13, 15, 2, 6, 16],
  ![11, 18, 22, 3, 21, 17, 13, 1, 10, 7, 12, 0, 20, 14, 16, 6, 2, 4, 9, 15, 5, 8, 19],
  ![0, 13, 2, 8, 5, 4, 19, 7, 3, 17, 15, 14, 12, 1, 11, 10, 16, 9, 18, 6, 22, 21, 20],
  ![4, 13, 15, 12, 5, 0, 22, 14, 10, 20, 2, 7, 8, 1, 11, 3, 18, 9, 16, 6, 19, 21, 17],
  ![0, 9, 22, 3, 12, 4, 16, 7, 8, 11, 15, 1, 5, 14, 17, 21, 19, 13, 18, 6, 2, 10, 20],
  ![18, 2, 15, 12, 22, 14, 5, 0, 3, 21, 13, 16, 6, 1, 11, 10, 4, 9, 7, 8, 19, 20, 17],
  ![13, 16, 6, 15, 2, 1, 22, 14, 8, 5, 19, 11, 10, 7, 0, 3, 9, 18, 17, 21, 20, 12, 4],
  ![1, 18, 22, 3, 15, 13, 17, 11, 10, 0, 6, 7, 2, 14, 4, 12, 20, 16, 9, 21, 19, 8, 5],
  ![9, 19, 6, 15, 22, 14, 2, 1, 3, 12, 16, 17, 21, 7, 0, 8, 13, 18, 11, 10, 20, 5, 4],
  ![2, 7, 8, 15, 13, 1, 5, 0, 6, 22, 19, 11, 3, 16, 14, 10, 9, 4, 17, 20, 21, 12, 18],
  ![1, 4, 5, 10, 15, 2, 17, 11, 3, 14, 8, 16, 13, 0, 18, 12, 21, 7, 9, 20, 19, 6, 22],
  ![7, 9, 22, 3, 6, 16, 4, 0, 8, 1, 21, 11, 19, 14, 13, 15, 5, 17, 18, 12, 20, 10, 2],
  ![18, 20, 21, 6, 22, 14, 19, 7, 3, 15, 17, 4, 12, 11, 1, 10, 16, 9, 0, 8, 5, 2, 13],
  ![9, 5, 12, 21, 22, 14, 20, 11, 3, 6, 4, 13, 15, 0, 7, 8, 17, 18, 1, 10, 2, 19, 16],
  ![9, 22, 12, 20, 5, 0, 21, 11, 10, 8, 18, 2, 15, 14, 16, 6, 17, 4, 1, 3, 13, 19, 7],
  ![18, 22, 15, 5, 2, 1, 12, 0, 8, 10, 9, 19, 6, 14, 17, 21, 4, 13, 7, 3, 16, 20, 11],
  ![4, 5, 15, 22, 13, 1, 12, 14, 6, 3, 9, 19, 8, 0, 17, 20, 18, 2, 16, 10, 7, 21, 11]]

def transversalInversePoint : Fin 23 → Fin 23 → Fin 23 :=
![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22],
  ![11, 0, 5, 3, 17, 20, 15, 1, 10, 18, 8, 7, 21, 4, 14, 12, 13, 16, 9, 2, 19, 6, 22],
  ![14, 0, 4, 8, 9, 22, 10, 13, 15, 18, 3, 7, 21, 5, 11, 12, 1, 16, 17, 2, 6, 19, 20],
  ![7, 14, 22, 8, 16, 6, 12, 0, 3, 17, 15, 13, 19, 9, 11, 21, 5, 1, 18, 4, 2, 10, 20],
  ![11, 14, 9, 15, 18, 20, 3, 5, 12, 17, 8, 13, 19, 22, 7, 21, 0, 1, 16, 4, 10, 2, 6],
  ![13, 7, 6, 8, 1, 2, 21, 14, 15, 18, 3, 0, 10, 16, 11, 19, 9, 5, 17, 22, 4, 12, 20],
  ![13, 11, 20, 15, 1, 10, 21, 14, 8, 16, 12, 5, 2, 18, 7, 19, 22, 0, 17, 9, 4, 3, 6],
  ![11, 7, 16, 3, 17, 20, 15, 9, 21, 18, 8, 0, 10, 6, 13, 19, 14, 5, 1, 22, 12, 4, 2],
  ![0, 13, 2, 8, 5, 4, 19, 7, 3, 17, 15, 14, 12, 1, 11, 10, 16, 9, 18, 6, 22, 21, 20],
  ![5, 13, 10, 15, 0, 4, 19, 11, 12, 17, 8, 14, 3, 1, 7, 2, 18, 22, 16, 20, 9, 21, 6],
  ![0, 11, 20, 3, 5, 12, 19, 7, 8, 1, 21, 9, 4, 17, 13, 10, 6, 14, 18, 16, 22, 15, 2],
  ![7, 13, 1, 8, 16, 6, 12, 18, 19, 17, 15, 14, 3, 10, 5, 2, 11, 22, 0, 20, 21, 9, 4],
  ![14, 5, 4, 15, 22, 9, 2, 13, 8, 16, 12, 11, 21, 0, 7, 3, 1, 18, 17, 10, 20, 19, 6],
  ![9, 0, 12, 3, 14, 22, 10, 11, 21, 18, 8, 7, 15, 5, 13, 4, 17, 6, 1, 20, 16, 19, 2],
  ![14, 7, 6, 8, 22, 21, 2, 13, 15, 0, 19, 18, 9, 16, 5, 3, 10, 11, 17, 1, 20, 12, 4],
  ![7, 5, 0, 12, 17, 6, 8, 1, 2, 16, 15, 11, 21, 4, 14, 3, 13, 18, 22, 10, 19, 20, 9],
  ![13, 0, 5, 8, 1, 2, 21, 17, 10, 18, 3, 7, 15, 12, 9, 4, 11, 6, 14, 20, 19, 16, 22],
  ![7, 9, 22, 3, 6, 16, 4, 0, 8, 1, 21, 11, 19, 14, 13, 15, 5, 17, 18, 12, 20, 10, 2],
  ![18, 14, 21, 8, 11, 20, 3, 7, 19, 17, 15, 13, 12, 22, 5, 9, 16, 10, 0, 6, 1, 2, 4],
  ![13, 18, 20, 8, 10, 1, 9, 14, 15, 0, 19, 7, 2, 11, 5, 12, 22, 16, 17, 21, 6, 3, 4],
  ![5, 18, 11, 19, 17, 4, 15, 22, 9, 0, 8, 7, 2, 20, 13, 12, 14, 16, 10, 21, 3, 6, 1],
  ![7, 5, 4, 19, 16, 3, 12, 18, 8, 10, 9, 22, 6, 17, 13, 2, 20, 14, 0, 11, 21, 15, 1],
  ![13, 5, 17, 9, 0, 1, 8, 20, 12, 10, 19, 22, 6, 4, 7, 2, 18, 14, 16, 11, 15, 21, 3]]

/-- The destination block of each original GAP row block. -/
def destination : Fin 2 → Fin 23 → Fin 23 :=
![![0, 2, 1, 4, 3, 7, 6, 5, 8, 11, 10, 9, 15, 16, 14, 12, 13, 17, 18, 20, 19, 22, 21],
  ![1, 0, 8, 2, 12, 3, 4, 17, 5, 6, 7, 19, 9, 10, 11, 15, 16, 13, 14, 18, 21, 20, 22]]

def sourceBlock : Fin 2 → Fin 23 → Fin 23 :=
![![0, 2, 1, 4, 3, 7, 6, 5, 8, 11, 10, 9, 15, 16, 14, 12, 13, 17, 18, 20, 19, 22, 21],
  ![1, 0, 3, 5, 6, 8, 9, 10, 2, 12, 13, 14, 4, 17, 18, 15, 16, 7, 19, 11, 21, 20, 22]]

/-- Coordinates of the 23 star vectors; the point-9 vector maps to zero. -/
def quotientMask : Fin 23 → ℕ :=
![512, 436, 972, 866, 250, 701, 315, 915, 109, 0, 542, 853, 715, 487, 1, 2, 4, 8, 16, 32, 64, 128, 256]

/-- The ten quotient representatives in the original saved ordering. -/
def quotientPoint : Fin 10 → Fin 23 := ![14,15,16,17,18,19,20,21,22,0]

/-- Direct action on quotient representatives, with columns as images. -/
def pointMatrix (g : Models.pointGroup) : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  fun x y => bit (quotientMask (g.val.val (quotientPoint y))) x.val

/-- The remaining local calculation concerns the literal native M22 cocode,
with its canonical marking and the explicit quotient basis above. -/
structure PointCoordinates where
  equiv : Models.Space false ≃ₗ[ZMod 2] (Fin 10 → ZMod 2)
  intertwines : ∀ g v,
    equiv (Models.pointAction canonicalMarking false g v) = (pointMatrix g).mulVec (equiv v)

end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison
