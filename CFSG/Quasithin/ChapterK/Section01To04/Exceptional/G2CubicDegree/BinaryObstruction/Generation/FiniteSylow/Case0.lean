module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.FiniteSylow.BasicMatrices

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

def recoveryLabel0 : Fin 4 → ℕ := ![9241422240497803929, 9241492057334482433, 9241492057334515265, 6955253306220413186]

private theorem conjugator_matrix : HasMatrix (conjugator 0).val 288587807843409470 := by
  apply Check.hasMatrix derivedLetter_matrix
  refine Check.cons (b := 307371864506565438) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9232484858079610369 (column 307371864506565438 c) r = column 288587807843409470 c r) c)
  refine Check.cons (b := 4613027474488507651) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 4665733663881429251 (column 4613027474488507651 c) r = column 307371864506565438 c r) c)
  refine Check.cons (b := 4665733663881429251) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9232484858079610369 (column 4665733663881429251 c) r = column 4613027474488507651 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 4665733663881429251 (column 9241421688590303745 c) r = column 4665733663881429251 c r) c)
  exact Check.nil

private theorem chosen_matrix : HasMatrix (chosen 0) 9241422240497836761 := by
  apply hasMatrix_of_columns
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    (chosen 0).val (basisVector c) r = column 9241422240497836761 c r) c)

private theorem inverse_matrix : HasMatrix (conjugator 0).val⁻¹ 4530865113921504320 := by
  apply conjugator_matrix.inv
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 288587807843409470 (column 4530865113921504320 c) r = basisVector (F := ZMod 2) c r) c)

private theorem product_matrix : HasMatrix ((conjugator 0).val * chosen 0) 4961239512790023902 := by
  apply conjugator_matrix.mul chosen_matrix
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 288587807843409470 (column 9241422240497836761 c) r = column 4961239512790023902 c r) c)

private theorem supplement_matrix : HasMatrix (supplement 0) 6955253306220413186 := by
  apply product_matrix.mul inverse_matrix
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 4961239512790023902 (column 4530865113921504320 c) r = column 6955253306220413186 c r) c)

private theorem recovery_matrix (j : Fin 4) : HasMatrix (recoveryLetter 0 j) (recoveryLabel0 j) := by
  fin_cases j
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 0 0).val (basisVector c) r = column 9241422240497803929 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 0 1).val (basisVector c) r = column 9241492057334482433 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 0 2).val (basisVector c) r = column 9241492057334515265 c r) c)
  · exact supplement_matrix

private theorem recover_c : word (recoveryLetter 0) [0] = basicLetter 0 := by
  apply HasMatrix.eq (n := 9241422240497803929) ?_ (basicLetter_matrix 0)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240497803929 (column 9241421688590303745 c) r = column 9241422240497803929 c r) c)
  exact Check.nil

private theorem recover_e : word (recoveryLetter 0) [1] = basicLetter 1 := by
  apply HasMatrix.eq (n := 9241492057334482433) ?_ (basicLetter_matrix 1)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334482433 (column 9241421688590303745 c) r = column 9241492057334482433 c r) c)
  exact Check.nil

private theorem recover_f : word (recoveryLetter 0) [1, 3, 0, 3, 1] = basicLetter 2 := by
  apply HasMatrix.eq (n := 9277450623588762115) ?_ (basicLetter_matrix 2)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9277661729821310467) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334482433 (column 9277661729821310467 c) r = column 9277450623588762115 c r) c)
  refine Check.cons (b := 2342437127828210494) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6955253306220413186 (column 2342437127828210494 c) r = column 9277661729821310467 c r) c)
  refine Check.cons (b := 2342436989843865862) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240497803929 (column 2342436989843865862 c) r = column 2342437127828210494 c r) c)
  refine Check.cons (b := 9241492057334482433) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6955253306220413186 (column 9241492057334482433 c) r = column 2342436989843865862 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334482433 (column 9241421688590303745 c) r = column 9241492057334482433 c r) c)
  exact Check.nil

private theorem recover_r : word (recoveryLetter 0) [1, 2, 3, 1, 2, 3, 1, 2] = basicLetter 3 := by
  apply HasMatrix.eq (n := 9232449673707521025) ?_ (basicLetter_matrix 3)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9232484858079610369) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334482433 (column 9232484858079610369 c) r = column 9232449673707521025 c r) c)
  refine Check.cons (b := 9232449673707553825) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334515265 (column 9232449673707553825 c) r = column 9232484858079610369 c r) c)
  refine Check.cons (b := 6919365246694007172) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6955253306220413186 (column 6919365246694007172 c) r = column 9232449673707553825 c r) c)
  refine Check.cons (b := 6919358649624248452) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334482433 (column 6919358649624248452 c) r = column 6919365246694007172 c r) c)
  refine Check.cons (b := 6919365246694015362) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334515265 (column 6919365246694015362 c) r = column 6919358649624248452 c r) c)
  refine Check.cons (b := 9241421688590336577) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6955253306220413186 (column 9241421688590336577 c) r = column 6919365246694015362 c r) c)
  refine Check.cons (b := 9241492057334515265) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334482433 (column 9241492057334515265 c) r = column 9241421688590336577 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334515265 (column 9241421688590303745 c) r = column 9241492057334515265 c r) c)
  exact Check.nil

private theorem recover_s : word (recoveryLetter 0) [1, 2, 3, 2, 3, 1, 3, 1, 3, 2, 3] = basicLetter 4 := by
  apply HasMatrix.eq (n := 4647719248123134210) ?_ (basicLetter_matrix 4)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 4647859985611497730) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334482433 (column 4647859985611497730 c) r = column 4647719248123134210 c r) c)
  refine Check.cons (b := 4647719248123150722) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334515265 (column 4647719248123150722 c) r = column 4647859985611497730 c r) c)
  refine Check.cons (b := 9520997808728343105) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6955253306220413186 (column 9520997808728343105 c) r = column 4647719248123150722 c r) c)
  refine Check.cons (b := 9520961524844626016) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334515265 (column 9520961524844626016 c) r = column 9520997808728343105 c r) c)
  refine Check.cons (b := 7026185000351457408) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6955253306220413186 (column 7026185000351457408 c) r = column 9520961524844626016 c r) c)
  refine Check.cons (b := 7026323538816548992) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334482433 (column 7026323538816548992 c) r = column 7026185000351457408 c r) c)
  refine Check.cons (b := 432732661174534208) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6955253306220413186 (column 432732661174534208 c) r = column 7026323538816548992 c r) c)
  refine Check.cons (b := 432733760686163008) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334482433 (column 432733760686163008 c) r = column 432732661174534208 c r) c)
  refine Check.cons (b := 6955387446639018116) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6955253306220413186 (column 6955387446639018116 c) r = column 432733760686163008 c r) c)
  refine Check.cons (b := 6955253306220413186) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334515265 (column 6955253306220413186 c) r = column 6955387446639018116 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6955253306220413186 (column 9241421688590303745 c) r = column 6955253306220413186 c r) c)
  exact Check.nil

theorem recover_case_0 (K : Subgroup G) (h : ∀ j, recoveryLetter 0 j ∈ K) :
    ∀ j, basicLetter j ∈ K := by
  intro j
  fin_cases j
  · change basicLetter 0 ∈ K
    rw [← recover_c]
    exact word_mem _ K h _
  · change basicLetter 1 ∈ K
    rw [← recover_e]
    exact word_mem _ K h _
  · change basicLetter 2 ∈ K
    rw [← recover_f]
    exact word_mem _ K h _
  · change basicLetter 3 ∈ K
    rw [← recover_r]
    exact word_mem _ K h _
  · change basicLetter 4 ∈ K
    rw [← recover_s]
    exact word_mem _ K h _

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.FiniteSylow
