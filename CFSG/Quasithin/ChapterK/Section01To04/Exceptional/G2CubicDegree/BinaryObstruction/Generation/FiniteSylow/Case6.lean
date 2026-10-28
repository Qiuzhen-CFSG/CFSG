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

def recoveryLabel6 : Fin 4 → ℕ := ![9241422240506192569, 9241633622690381373, 9241633622690414205, 6826055205333893378]

private theorem conjugator_matrix : HasMatrix (conjugator 6).val 288587807843409470 := by
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

private theorem chosen_matrix : HasMatrix (chosen 6) 9241422240506192569 := by
  apply hasMatrix_of_columns
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    (chosen 6).val (basisVector c) r = column 9241422240506192569 c r) c)

private theorem inverse_matrix : HasMatrix (conjugator 6).val⁻¹ 4530865113921504320 := by
  apply conjugator_matrix.inv
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 288587807843409470 (column 4530865113921504320 c) r = basisVector (F := ZMod 2) c r) c)

private theorem product_matrix : HasMatrix ((conjugator 6).val * chosen 6) 14175429394362482398 := by
  apply conjugator_matrix.mul chosen_matrix
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 288587807843409470 (column 9241422240506192569 c) r = column 14175429394362482398 c r) c)

private theorem supplement_matrix : HasMatrix (supplement 6) 6826055205333893378 := by
  apply product_matrix.mul inverse_matrix
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 14175429394362482398 (column 4530865113921504320 c) r = column 6826055205333893378 c r) c)

private theorem recovery_matrix (j : Fin 4) : HasMatrix (recoveryLetter 6 j) (recoveryLabel6 j) := by
  fin_cases j
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 6 0).val (basisVector c) r = column 9241422240506192569 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 6 1).val (basisVector c) r = column 9241633622690381373 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 6 2).val (basisVector c) r = column 9241633622690414205 c r) c)
  · exact supplement_matrix

private theorem recover_c : word (recoveryLetter 6) [3, 1, 2, 3, 0, 3, 0, 3, 1, 2, 3] = basicLetter 0 := by
  apply HasMatrix.eq (n := 9241422240497803929) ?_ (basicLetter_matrix 0)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 4468658467116325154) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 4468658467116325154 c) r = column 9241422240497803929 c r) c)
  refine Check.cons (b := 4468661606389079781) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690381373 (column 4468661606389079781 c) r = column 4468658467116325154 c r) c)
  refine Check.cons (b := 4468658467116328737) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690414205 (column 4468658467116328737 c) r = column 4468661606389079781 c r) c)
  refine Check.cons (b := 13726166468276134311) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 13726166468276134311 c) r = column 4468658467116328737 c r) c)
  refine Check.cons (b := 13726165804003164706) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 13726165804003164706 c) r = column 13726166468276134311 c r) c)
  refine Check.cons (b := 16043399857420968450) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 16043399857420968450 c) r = column 13726165804003164706 c r) c)
  refine Check.cons (b := 16043400728128698719) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 16043400728128698719 c) r = column 16043399857420968450 c r) c)
  refine Check.cons (b := 6826055205333917625) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 6826055205333917625 c) r = column 16043400728128698719 c r) c)
  refine Check.cons (b := 6826296977157218438) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690381373 (column 6826296977157218438 c) r = column 6826055205333917625 c r) c)
  refine Check.cons (b := 6826055205333893378) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690414205 (column 6826055205333893378 c) r = column 6826296977157218438 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 9241421688590303745 c) r = column 6826055205333893378 c r) c)
  exact Check.nil

private theorem recover_e : word (recoveryLetter 6) [3, 2, 3, 1, 2, 3, 2, 3] = basicLetter 1 := by
  apply HasMatrix.eq (n := 9241492057334482433) ?_ (basicLetter_matrix 1)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 6556965144849940742) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 6556965144849940742 c) r = column 9241492057334482433 c r) c)
  refine Check.cons (b := 6557136237478748290) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690414205 (column 6557136237478748290 c) r = column 6556965144849940742 c r) c)
  refine Check.cons (b := 306316311779115552) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 306316311779115552 c) r = column 6557136237478748290 c r) c)
  refine Check.cons (b := 306250634284522489) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690381373 (column 306250634284522489 c) r = column 306316311779115552 c r) c)
  refine Check.cons (b := 306316311779116640) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690414205 (column 306316311779116640 c) r = column 306250634284522489 c r) c)
  refine Check.cons (b := 6826296977157218438) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 6826296977157218438 c) r = column 306316311779116640 c r) c)
  refine Check.cons (b := 6826055205333893378) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690414205 (column 6826055205333893378 c) r = column 6826296977157218438 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 9241421688590303745 c) r = column 6826055205333893378 c r) c)
  exact Check.nil

private theorem recover_f : word (recoveryLetter 6) [0, 1, 3, 1, 2, 3, 1, 2, 3, 0, 2] = basicLetter 2 := by
  apply HasMatrix.eq (n := 9277450623588762115) ?_ (basicLetter_matrix 2)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9277451175496262331) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 9277451175496262331 c) r = column 9277450623588762115 c r) c)
  refine Check.cons (b := 9277521820187911935) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690381373 (column 9277521820187911935 c) r = column 9277451175496262331 c r) c)
  refine Check.cons (b := 9395005189532352358) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 9395005189532352358 c) r = column 9277521820187911935 c r) c)
  refine Check.cons (b := 9394826111439151803) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690381373 (column 9394826111439151803 c) r = column 9395005189532352358 c r) c)
  refine Check.cons (b := 9395005189532318983) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690414205 (column 9395005189532318983 c) r = column 9394826111439151803 c r) c)
  refine Check.cons (b := 153967993573738365) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 153967993573738365 c) r = column 9395005189532318983 c r) c)
  refine Check.cons (b := 154002212096286938) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690381373 (column 154002212096286938 c) r = column 153967993573738365 c r) c)
  refine Check.cons (b := 153967993573737822) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690414205 (column 153967993573737822 c) r = column 154002212096286938 c r) c)
  refine Check.cons (b := 9241633070774509061) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 9241633070774509061 c) r = column 153967993573737822 c r) c)
  refine Check.cons (b := 9241633622690414205) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 9241633622690414205 c) r = column 9241633070774509061 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690414205 (column 9241421688590303745 c) r = column 9241633622690414205 c r) c)
  exact Check.nil

private theorem recover_r : word (recoveryLetter 6) [3, 0, 3, 1, 2, 3, 0, 3] = basicLetter 3 := by
  apply HasMatrix.eq (n := 9232449673707521025) ?_ (basicLetter_matrix 3)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 4529780154930823428) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 4529780154930823428 c) r = column 9232449673707521025 c r) c)
  refine Check.cons (b := 4529780318515167777) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 4529780318515167777 c) r = column 4529780154930823428 c r) c)
  refine Check.cons (b := 6919365246687715586) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 6919365246687715586 c) r = column 4529780318515167777 c r) c)
  refine Check.cons (b := 6919464642538880669) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690381373 (column 6919464642538880669 c) r = column 6919365246687715586 c r) c)
  refine Check.cons (b := 6919365246687723780) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690414205 (column 6919365246687723780 c) r = column 6919464642538880669 c r) c)
  refine Check.cons (b := 6826055524145366081) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 6826055524145366081 c) r = column 6919365246687723780 c r) c)
  refine Check.cons (b := 6826055205333893378) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 6826055205333893378 c) r = column 6826055524145366081 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 9241421688590303745 c) r = column 6826055205333893378 c r) c)
  exact Check.nil

private theorem recover_s : word (recoveryLetter 6) [1, 3, 0, 3, 0, 2, 3, 0, 1, 3, 0, 3, 0, 3] = basicLetter 4 := by
  apply HasMatrix.eq (n := 4647719248123134210) ?_ (basicLetter_matrix 4)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 4647931182223211838) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690381373 (column 4647931182223211838 c) r = column 4647719248123134210 c r) c)
  refine Check.cons (b := 5016973511155596861) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 5016973511155596861 c) r = column 4647931182223211838 c r) c)
  refine Check.cons (b := 5016973248125198526) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 5016973248125198526 c) r = column 5016973511155596861 c r) c)
  refine Check.cons (b := 4962295884470468320) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 4962295884470468320 c) r = column 5016973248125198526 c r) c)
  refine Check.cons (b := 4962295625772639009) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 4962295625772639009 c) r = column 4962295884470468320 c r) c)
  refine Check.cons (b := 4962126818669643230) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690414205 (column 4962126818669643230 c) r = column 4962295625772639009 c r) c)
  refine Check.cons (b := 13746077390675762757) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 13746077390675762757 c) r = column 4962126818669643230 c r) c)
  refine Check.cons (b := 13746076985102974467) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 13746076985102974467 c) r = column 13746077390675762757 c r) c)
  refine Check.cons (b := 13746003443133315783) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690381373 (column 13746003443133315783 c) r = column 13746076985102974467 c r) c)
  refine Check.cons (b := 6919365660621916154) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 6919365660621916154 c) r = column 13746003443133315783 c r) c)
  refine Check.cons (b := 6919365246687723780) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 6919365246687723780 c) r = column 6919365660621916154 c r) c)
  refine Check.cons (b := 6826055524145366081) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 6826055524145366081 c) r = column 6919365246687723780 c r) c)
  refine Check.cons (b := 6826055205333893378) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 6826055205333893378 c) r = column 6826055524145366081 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 9241421688590303745 c) r = column 6826055205333893378 c r) c)
  exact Check.nil

theorem recover_case_6 (K : Subgroup G) (h : ∀ j, recoveryLetter 6 j ∈ K) :
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
