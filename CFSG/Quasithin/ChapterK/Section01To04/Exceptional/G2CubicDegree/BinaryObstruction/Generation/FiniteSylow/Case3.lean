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

def recoveryLabel3 : Fin 4 → ℕ := ![9277450623588762115, 9277450623597150755, 9241421688598725217, 2566979866465788126]

private theorem conjugator_matrix : HasMatrix (conjugator 3).val 307371864506565438 := by
  apply Check.hasMatrix derivedLetter_matrix
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

private theorem chosen_matrix : HasMatrix (chosen 3) 9277450623588795075 := by
  apply hasMatrix_of_columns
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    (chosen 3).val (basisVector c) r = column 9277450623588795075 c r) c)

private theorem inverse_matrix : HasMatrix (conjugator 3).val⁻¹ 8989391223647117856 := by
  apply conjugator_matrix.inv
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 307371864506565438 (column 8989391223647117856 c) r = basisVector (F := ZMod 2) c r) c)

private theorem product_matrix : HasMatrix ((conjugator 3).val * chosen 3) 4394602633850470790 := by
  apply conjugator_matrix.mul chosen_matrix
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 307371864506565438 (column 9277450623588795075 c) r = column 4394602633850470790 c r) c)

private theorem supplement_matrix : HasMatrix (supplement 3) 2566979866465788126 := by
  apply product_matrix.mul inverse_matrix
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 4394602633850470790 (column 8989391223647117856 c) r = column 2566979866465788126 c r) c)

private theorem recovery_matrix (j : Fin 4) : HasMatrix (recoveryLetter 3 j) (recoveryLabel3 j) := by
  fin_cases j
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 3 0).val (basisVector c) r = column 9277450623588762115 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 3 1).val (basisVector c) r = column 9277450623597150755 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 3 2).val (basisVector c) r = column 9241421688598725217 c r) c)
  · exact supplement_matrix

private theorem recover_c : word (recoveryLetter 3) [0, 1, 3, 1, 3, 1, 3, 2, 3, 2, 3, 1, 3, 1, 3] = basicLetter 0 := by
  apply HasMatrix.eq (n := 9241422240497803929) ?_ (basicLetter_matrix 0)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9277451175496262331) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623588762115 (column 9277451175496262331 c) r = column 9241422240497803929 c r) c)
  refine Check.cons (b := 9241422240506192569) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623597150755 (column 9241422240506192569 c) r = column 9277451175496262331 c r) c)
  refine Check.cons (b := 13530888020109942846) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 13530888020109942846 c) r = column 9241422240506192569 c r) c)
  refine Check.cons (b := 13509777060817592448) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623597150755 (column 13509777060817592448 c) r = column 13530888020109942846 c r) c)
  refine Check.cons (b := 4468658467120126463) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 4468658467120126463 c) r = column 13509777060817592448 c r) c)
  refine Check.cons (b := 4484984822343113147) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623597150755 (column 4484984822343113147 c) r = column 4468658467120126463 c r) c)
  refine Check.cons (b := 18429756131955039813) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 18429756131955039813 c) r = column 4484984822343113147 c r) c)
  refine Check.cons (b := 18429756131963183395) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598725217 (column 18429756131963183395 c) r = column 18429756131955039813 c r) c)
  refine Check.cons (b := 12059476445619984827) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 12059476445619984827 c) r = column 18429756131963183395 c r) c)
  refine Check.cons (b := 12059476445630119485) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598725217 (column 12059476445630119485 c) r = column 12059476445619984827 c r) c)
  refine Check.cons (b := 16016389681643987235) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 16016389681643987235 c) r = column 12059476445630119485 c r) c)
  refine Check.cons (b := 16040596102784491943) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623597150755 (column 16040596102784491943 c) r = column 16016389681643987235 c r) c)
  refine Check.cons (b := 2575142166774997120) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 2575142166774997120 c) r = column 16040596102784491943 c r) c)
  refine Check.cons (b := 2566979866465788126) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623597150755 (column 2566979866465788126 c) r = column 2575142166774997120 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 9241421688590303745 c) r = column 2566979866465788126 c r) c)
  exact Check.nil

private theorem recover_e : word (recoveryLetter 3) [0, 3, 0, 1, 2, 3, 1, 3, 0, 2, 3, 1, 3, 0] = basicLetter 1 := by
  apply HasMatrix.eq (n := 9241492057334482433) ?_ (basicLetter_matrix 1)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9277521268288783879) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623588762115 (column 9277521268288783879 c) r = column 9241492057334482433 c r) c)
  refine Check.cons (b := 7054187923024584738) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 7054187923024584738 c) r = column 9277521268288783879 c r) c)
  refine Check.cons (b := 7026884289746771970) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623588762115 (column 7026884289746771970 c) r = column 7054187923024584738 c r) c)
  refine Check.cons (b := 7054187923026616480) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623597150755 (column 7054187923026616480 c) r = column 7026884289746771970 c r) c)
  refine Check.cons (b := 7054187923024593351) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598725217 (column 7054187923024593351 c) r = column 7054187923026616480 c r) c)
  refine Check.cons (b := 307371847255131750) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 307371847255131750 c) r = column 7054187923024593351 c r) c)
  refine Check.cons (b := 306245943035168353) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623597150755 (column 306245943035168353 c) r = column 307371847255131750 c r) c)
  refine Check.cons (b := 7421826179916973534) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 7421826179916973534 c) r = column 306245943035168353 c r) c)
  refine Check.cons (b := 7393115124596360603) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623588762115 (column 7393115124596360603 c) r = column 7421826179916973534 c r) c)
  refine Check.cons (b := 7393115124598580125) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598725217 (column 7393115124598580125 c) r = column 7393115124596360603 c r) c)
  refine Check.cons (b := 2415202669367943296) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 2415202669367943296 c) r = column 7393115124598580125 c r) c)
  refine Check.cons (b := 2424491921385676902) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623597150755 (column 2424491921385676902 c) r = column 2415202669367943296 c r) c)
  refine Check.cons (b := 9277450623588762115) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 9277450623588762115 c) r = column 2424491921385676902 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623588762115 (column 9241421688590303745 c) r = column 9277450623588762115 c r) c)
  exact Check.nil

private theorem recover_f : word (recoveryLetter 3) [0] = basicLetter 2 := by
  apply HasMatrix.eq (n := 9277450623588762115) ?_ (basicLetter_matrix 2)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623588762115 (column 9241421688590303745 c) r = column 9277450623588762115 c r) c)
  exact Check.nil

private theorem recover_r : word (recoveryLetter 3) [0, 3, 1, 3, 2, 3, 1, 3, 0] = basicLetter 3 := by
  apply HasMatrix.eq (n := 9232449673707521025) ?_ (basicLetter_matrix 3)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9268478746683900933) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623588762115 (column 9268478746683900933 c) r = column 9232449673707521025 c r) c)
  refine Check.cons (b := 4738779179900690534) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 4738779179900690534 c) r = column 9268478746683900933 c r) c)
  refine Check.cons (b := 4720482728626118784) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623597150755 (column 4720482728626118784 c) r = column 4738779179900690534 c r) c)
  refine Check.cons (b := 7393115124596360603) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 7393115124596360603 c) r = column 4720482728626118784 c r) c)
  refine Check.cons (b := 7393115124598580125) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598725217 (column 7393115124598580125 c) r = column 7393115124596360603 c r) c)
  refine Check.cons (b := 2415202669367943296) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 2415202669367943296 c) r = column 7393115124598580125 c r) c)
  refine Check.cons (b := 2424491921385676902) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623597150755 (column 2424491921385676902 c) r = column 2415202669367943296 c r) c)
  refine Check.cons (b := 9277450623588762115) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 9277450623588762115 c) r = column 2424491921385676902 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623588762115 (column 9241421688590303745 c) r = column 9277450623588762115 c r) c)
  exact Check.nil

private theorem recover_s : word (recoveryLetter 3) [1, 3, 1, 2, 3, 0, 3, 1, 3, 1] = basicLetter 4 := by
  apply HasMatrix.eq (n := 4647719248123134210) ?_ (basicLetter_matrix 4)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 4665733663885623559) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623597150755 (column 4665733663885623559 c) r = column 4647719248123134210 c r) c)
  refine Check.cons (b := 153721832321287397) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 153721832321287397 c) r = column 4665733663885623559 c r) c)
  refine Check.cons (b := 153158740076430400) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623597150755 (column 153158740076430400 c) r = column 153721832321287397 c r) c)
  refine Check.cons (b := 153158740076561985) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598725217 (column 153158740076561985 c) r = column 153158740076430400 c r) c)
  refine Check.cons (b := 16600056115482526526) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 16600056115482526526 c) r = column 153158740076561985 c r) c)
  refine Check.cons (b := 16625388945576035133) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623588762115 (column 16625388945576035133 c) r = column 16600056115482526526 c r) c)
  refine Check.cons (b := 73190125646930048) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 73190125646930048 c) r = column 16625388945576035133 c r) c)
  refine Check.cons (b := 73471626496139494) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623597150755 (column 73471626496139494 c) r = column 73190125646930048 c r) c)
  refine Check.cons (b := 9277450623597150755) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 2566979866465788126 (column 9277450623597150755 c) r = column 73471626496139494 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277450623597150755 (column 9241421688590303745 c) r = column 9277450623597150755 c r) c)
  exact Check.nil

theorem recover_case_3 (K : Subgroup G) (h : ∀ j, recoveryLetter 3 j ∈ K) :
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
