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

def recoveryLabel2 : Fin 4 → ℕ := ![9241492057334482433, 9241633070774541893, 9241633070774509061, 6946493363409346492]

private theorem conjugator_matrix : HasMatrix (conjugator 2).val 2306584123302574855 := by
  apply Check.hasMatrix derivedLetter_matrix
  refine Check.cons (b := 2350881247770312967) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9232484858079610369 (column 2350881247770312967 c) r = column 2306584123302574855 c r) c)
  refine Check.cons (b := 9232484858079610369) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 4665733663881429251 (column 9232484858079610369 c) r = column 2350881247770312967 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9232484858079610369 (column 9241421688590303745 c) r = column 9232484858079610369 c r) c)
  exact Check.nil

private theorem chosen_matrix : HasMatrix (chosen 2) 9241562702030363205 := by
  apply hasMatrix_of_columns
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    (chosen 2).val (basisVector c) r = column 9241562702030363205 c r) c)

private theorem inverse_matrix : HasMatrix (conjugator 2).val⁻¹ 16203529557398339588 := by
  apply conjugator_matrix.inv
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 2306584123302574855 (column 16203529557398339588 c) r = basisVector (F := ZMod 2) c r) c)

private theorem product_matrix : HasMatrix ((conjugator 2).val * chosen 2) 11590852098283366299 := by
  apply conjugator_matrix.mul chosen_matrix
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 2306584123302574855 (column 9241562702030363205 c) r = column 11590852098283366299 c r) c)

private theorem supplement_matrix : HasMatrix (supplement 2) 6946493363409346492 := by
  apply product_matrix.mul inverse_matrix
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 11590852098283366299 (column 16203529557398339588 c) r = column 6946493363409346492 c r) c)

private theorem recovery_matrix (j : Fin 4) : HasMatrix (recoveryLetter 2 j) (recoveryLabel2 j) := by
  fin_cases j
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 2 0).val (basisVector c) r = column 9241492057334482433 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 2 1).val (basisVector c) r = column 9241633070774541893 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 2 2).val (basisVector c) r = column 9241633070774509061 c r) c)
  · exact supplement_matrix

private theorem recover_c : word (recoveryLetter 2) [3, 1, 3, 0, 2, 3, 0, 2, 3, 1, 3] = basicLetter 0 := by
  apply HasMatrix.eq (n := 9241422240497803929) ?_ (basicLetter_matrix 0)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 6919365660621907964) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6946493363409346492 (column 6919365660621907964 c) r = column 9241422240497803929 c r) c)
  refine Check.cons (b := 6919464642538880669) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633070774541893 (column 6919464642538880669 c) r = column 6919365660621907964 c r) c)
  refine Check.cons (b := 16591085040549255935) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6946493363409346492 (column 16591085040549255935 c) r = column 6919464642538880669 c r) c)
  refine Check.cons (b := 16591086140060886783) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334482433 (column 16591086140060886783 c) r = column 16591085040549255935 c r) c)
  refine Check.cons (b := 16591183854576631235) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633070774509061 (column 16591183854576631235 c) r = column 16591086140060886783 c r) c)
  refine Check.cons (b := 9711768194254677371) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6946493363409346492 (column 9711768194254677371 c) r = column 16591183854576631235 c r) c)
  refine Check.cons (b := 9711984798045362555) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334482433 (column 9711984798045362555 c) r = column 9711768194254677371 c r) c)
  refine Check.cons (b := 9711915222678927879) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633070774509061 (column 9711915222678927879 c) r = column 9711984798045362555 c r) c)
  refine Check.cons (b := 6946486378282606149) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6946493363409346492 (column 6946486378282606149 c) r = column 9711915222678927879 c r) c)
  refine Check.cons (b := 6946493363409346492) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633070774541893 (column 6946493363409346492 c) r = column 6946486378282606149 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6946493363409346492 (column 9241421688590303745 c) r = column 6946493363409346492 c r) c)
  exact Check.nil

private theorem recover_e : word (recoveryLetter 2) [0] = basicLetter 1 := by
  apply HasMatrix.eq (n := 9241492057334482433) ?_ (basicLetter_matrix 1)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334482433 (column 9241421688590303745 c) r = column 9241492057334482433 c r) c)
  exact Check.nil

private theorem recover_f : word (recoveryLetter 2) [1, 2, 3, 0, 2, 3, 0, 2, 3] = basicLetter 2 := by
  apply HasMatrix.eq (n := 9277450623588762115) ?_ (basicLetter_matrix 2)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9277521820187911935) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633070774541893 (column 9277521820187911935 c) r = column 9277450623588762115 c r) c)
  refine Check.cons (b := 9277450623588795075) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633070774509061 (column 9277450623588795075 c) r = column 9277521820187911935 c r) c)
  refine Check.cons (b := 16167604114482898308) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6946493363409346492 (column 16167604114482898308 c) r = column 9277450623588795075 c r) c)
  refine Check.cons (b := 16167500760389861508) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334482433 (column 16167500760389861508 c) r = column 16167604114482898308 c r) c)
  refine Check.cons (b := 16167427976766808929) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633070774509061 (column 16167427976766808929 c) r = column 16167500760389861508 c r) c)
  refine Check.cons (b := 6946387422236057891) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6946493363409346492 (column 6946387422236057891 c) r = column 16167427976766808929 c r) c)
  refine Check.cons (b := 6946486378282597923) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334482433 (column 6946486378282597923 c) r = column 6946387422236057891 c r) c)
  refine Check.cons (b := 6946493363409346492) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633070774509061 (column 6946493363409346492 c) r = column 6946486378282597923 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6946493363409346492 (column 9241421688590303745 c) r = column 6946493363409346492 c r) c)
  exact Check.nil

private theorem recover_r : word (recoveryLetter 2) [3, 1, 2, 3] = basicLetter 3 := by
  apply HasMatrix.eq (n := 9232449673707521025) ?_ (basicLetter_matrix 3)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 6946493363409338330) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6946493363409346492 (column 6946493363409338330 c) r = column 9232449673707521025 c r) c)
  refine Check.cons (b := 6946486378282597923) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633070774541893 (column 6946486378282597923 c) r = column 6946493363409338330 c r) c)
  refine Check.cons (b := 6946493363409346492) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633070774509061 (column 6946493363409346492 c) r = column 6946486378282597923 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6946493363409346492 (column 9241421688590303745 c) r = column 6946493363409346492 c r) c)
  exact Check.nil

private theorem recover_s : word (recoveryLetter 2) [3, 1, 3, 1, 3, 0, 3, 1, 3, 1, 2, 3, 2, 3] = basicLetter 4 := by
  apply HasMatrix.eq (n := 4647719248123134210) ?_ (basicLetter_matrix 4)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9558298486290234236) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6946493363409346492 (column 9558298486290234236 c) r = column 4647719248123134210 c r) c)
  refine Check.cons (b := 9558261775543826850) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633070774541893 (column 9558261775543826850 c) r = column 9558298486290234236 c r) c)
  refine Check.cons (b := 7053595294880800035) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6946493363409346492 (column 7053595294880800035 c) r = column 9558261775543826850 c r) c)
  refine Check.cons (b := 7053733708305316732) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633070774541893 (column 7053733708305316732 c) r = column 7053595294880800035 c r) c)
  refine Check.cons (b := 432732661174403104) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6946493363409346492 (column 432732661174403104 c) r = column 7053733708305316732 c r) c)
  refine Check.cons (b := 432733760686031392) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492057334482433 (column 432733760686031392 c) r = column 432732661174403104 c r) c)
  refine Check.cons (b := 6980832784537270653) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6946493363409346492 (column 6980832784537270653 c) r = column 432733760686031392 c r) c)
  refine Check.cons (b := 6980692185024732963) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633070774541893 (column 6980692185024732963 c) r = column 6980832784537270653 c r) c)
  refine Check.cons (b := 9702943207796177568) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6946493363409346492 (column 9702943207796177568 c) r = column 6980692185024732963 c r) c)
  refine Check.cons (b := 9702977736766306685) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633070774541893 (column 9702977736766306685 c) r = column 9702943207796177568 c r) c)
  refine Check.cons (b := 9702943207796145159) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633070774509061 (column 9702943207796145159 c) r = column 9702977736766306685 c r) c)
  refine Check.cons (b := 6946486378282597923) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6946493363409346492 (column 6946486378282597923 c) r = column 9702943207796145159 c r) c)
  refine Check.cons (b := 6946493363409346492) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633070774509061 (column 6946493363409346492 c) r = column 6946486378282597923 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6946493363409346492 (column 9241421688590303745 c) r = column 6946493363409346492 c r) c)
  exact Check.nil

theorem recover_case_2 (K : Subgroup G) (h : ∀ j, recoveryLetter 2 j ∈ K) :
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
