module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.FiniteSylow.WitnessData

/-!
# Matrix certificates for the binary G₂ Sylow supplements

These identities concern the original split-octonion automorphisms. Each
matrix product is checked on eight basis columns. Candidate labels and words
from the retained exploration have no authority without these checks.
Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.3,
manuscript pp.10--11. Root coordinates: Gerald Höhn and the ATLAS contributors,
ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.FiniteSylow
open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion Certificate

def basicLetter : Fin 5 → G := ![rootC 1, rootE 1, rootF 1, weylR, weylS]

def basicLabel : Fin 5 → ℕ := ![9241422240497803929, 9241492057334482433, 9277450623588762115, 9232449673707521025, 4647719248123134210]

def derivedLabel : Fin 3 → ℕ := ![9277662281737232027, 4665733663881429251, 9232484858079610369]

theorem basicLetter_matrix (i : Fin 5) :
    HasMatrix (basicLetter i) (basicLabel i) := by
  fin_cases i
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (basicLetter 0).val (basisVector c) r = column 9241422240497803929 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (basicLetter 1).val (basisVector c) r = column 9241492057334482433 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (basicLetter 2).val (basisVector c) r = column 9277450623588762115 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (basicLetter 3).val (basisVector c) r = column 9232449673707521025 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (basicLetter 4).val (basisVector c) r = column 4647719248123134210 c r) c)

theorem derivedLetter_matrix (i : Fin 3) :
    HasMatrix (derivedLetter i) (derivedLabel i) := by
  fin_cases i
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (derivedLetter 0).val (basisVector c) r = column 9277662281737232027 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (derivedLetter 1).val (basisVector c) r = column 4665733663881429251 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (derivedLetter 2).val (basisVector c) r = column 9232484858079610369 c r) c)

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.FiniteSylow
