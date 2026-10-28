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

def recoveryLabel4 : Fin 4 → ℕ := ![9241492609241999001, 9241633622690381373, 9241633622690414205, 6826055205333893378]

private theorem conjugator_matrix : HasMatrix (conjugator 4).val 2306584123302574855 := by
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

private theorem chosen_matrix : HasMatrix (chosen 4) 9241492609242031833 := by
  apply hasMatrix_of_columns
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    (chosen 4).val (basisVector c) r = column 9241492609242031833 c r) c)

private theorem inverse_matrix : HasMatrix (conjugator 4).val⁻¹ 16203529557398339588 := by
  apply conjugator_matrix.inv
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 2306584123302574855 (column 16203529557398339588 c) r = basisVector (F := ZMod 2) c r) c)

private theorem product_matrix : HasMatrix ((conjugator 4).val * chosen 4) 6982275343794636667 := by
  apply conjugator_matrix.mul chosen_matrix
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 2306584123302574855 (column 9241492609242031833 c) r = column 6982275343794636667 c r) c)

private theorem supplement_matrix : HasMatrix (supplement 4) 6826055205333893378 := by
  apply product_matrix.mul inverse_matrix
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 6982275343794636667 (column 16203529557398339588 c) r = column 6826055205333893378 c r) c)

private theorem recovery_matrix (j : Fin 4) : HasMatrix (recoveryLetter 4 j) (recoveryLabel4 j) := by
  fin_cases j
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 4 0).val (basisVector c) r = column 9241492609241999001 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 4 1).val (basisVector c) r = column 9241633622690381373 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 4 2).val (basisVector c) r = column 9241633622690414205 c r) c)
  · exact supplement_matrix

private theorem recover_c : word (recoveryLetter 4) [0, 3, 2, 3, 1, 2, 3, 2, 3] = basicLetter 0 := by
  apply HasMatrix.eq (n := 9241422240497803929) ?_ (basicLetter_matrix 0)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9241492057334482433) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492609241999001 (column 9241492057334482433 c) r = column 9241422240497803929 c r) c)
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

private theorem recover_e : word (recoveryLetter 4) [3, 2, 3, 1, 2, 3, 2, 3] = basicLetter 1 := by
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

private theorem recover_f : word (recoveryLetter 4) [0, 3, 1, 2, 3, 1, 2, 3, 0] = basicLetter 2 := by
  apply HasMatrix.eq (n := 9277450623588762115) ?_ (basicLetter_matrix 2)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9277662281737232027) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492609241999001 (column 9277662281737232027 c) r = column 9277450623588762115 c r) c)
  refine Check.cons (b := 18031682754780765150) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 18031682754780765150 c) r = column 9277662281737232027 c r) c)
  refine Check.cons (b := 18031744586165639839) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690381373 (column 18031744586165639839 c) r = column 18031682754780765150 c r) c)
  refine Check.cons (b := 18031682754780750307) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690414205 (column 18031682754780750307 c) r = column 18031744586165639839 c r) c)
  refine Check.cons (b := 8793240302497751905) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 8793240302497751905 c) r = column 18031682754780750307 c r) c)
  refine Check.cons (b := 8793172762584359074) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690381373 (column 8793172762584359074 c) r = column 8793240302497751905 c r) c)
  refine Check.cons (b := 8793240302497732966) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690414205 (column 8793240302497732966 c) r = column 8793172762584359074 c r) c)
  refine Check.cons (b := 9241492609241999001) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 9241492609241999001 c) r = column 8793240302497732966 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492609241999001 (column 9241421688590303745 c) r = column 9241492609241999001 c r) c)
  exact Check.nil

private theorem recover_r : word (recoveryLetter 4) [0, 3, 0, 2, 3, 2, 3, 0, 2, 3, 0] = basicLetter 3 := by
  apply HasMatrix.eq (n := 9232449673707521025) ?_ (basicLetter_matrix 3)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9232485409985029785) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492609241999001 (column 9232485409985029785 c) r = column 9232449673707521025 c r) c)
  refine Check.cons (b := 8937318107178244454) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 8937318107178244454 c) r = column 9232485409985029785 c r) c)
  refine Check.cons (b := 8937318741289542402) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492609241999001 (column 8937318741289542402 c) r = column 8937318107178244454 c r) c)
  refine Check.cons (b := 8937331271143193248) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690414205 (column 8937331271143193248 c) r = column 8937318741289542402 c r) c)
  refine Check.cons (b := 11527484630223397114) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 11527484630223397114 c) r = column 8937331271143193248 c r) c)
  refine Check.cons (b := 11527451791475851516) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690414205 (column 11527451791475851516 c) r = column 11527484630223397114 c r) c)
  refine Check.cons (b := 8793180898695380160) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 8793180898695380160 c) r = column 11527451791475851516 c r) c)
  refine Check.cons (b := 8793172762584359074) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492609241999001 (column 8793172762584359074 c) r = column 8793180898695380160 c r) c)
  refine Check.cons (b := 8793240302497732966) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690414205 (column 8793240302497732966 c) r = column 8793172762584359074 c r) c)
  refine Check.cons (b := 9241492609241999001) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 9241492609241999001 c) r = column 8793240302497732966 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492609241999001 (column 9241421688590303745 c) r = column 9241492609241999001 c r) c)
  exact Check.nil

private theorem recover_s : word (recoveryLetter 4) [1, 3, 0, 3, 0, 2, 3, 0, 2, 3, 0, 3] = basicLetter 4 := by
  apply HasMatrix.eq (n := 4647719248123134210) ?_ (basicLetter_matrix 4)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 4647931182223211838) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690381373 (column 4647931182223211838 c) r = column 4647719248123134210 c r) c)
  refine Check.cons (b := 5016973511155596861) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 5016973511155596861 c) r = column 4647931182223211838 c r) c)
  refine Check.cons (b := 5016800624804005472) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492609241999001 (column 5016800624804005472 c) r = column 5016973511155596861 c r) c)
  refine Check.cons (b := 7492307975722721414) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 7492307975722721414 c) r = column 5016800624804005472 c r) c)
  refine Check.cons (b := 7492578071828847609) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492609241999001 (column 7492578071828847609 c) r = column 7492307975722721414 c r) c)
  refine Check.cons (b := 7492408212103161306) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690414205 (column 7492408212103161306 c) r = column 7492578071828847609 c r) c)
  refine Check.cons (b := 12043041799284251365) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 12043041799284251365 c) r = column 7492408212103161306 c r) c)
  refine Check.cons (b := 12043007011611542874) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492609241999001 (column 12043007011611542874 c) r = column 12043041799284251365 c r) c)
  refine Check.cons (b := 12043150508641436829) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241633622690414205 (column 12043150508641436829 c) r = column 12043007011611542874 c r) c)
  refine Check.cons (b := 6826258933793529156) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 6826258933793529156 c) r = column 12043150508641436829 c r) c)
  refine Check.cons (b := 6826055205333893378) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241492609241999001 (column 6826055205333893378 c) r = column 6826258933793529156 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 6826055205333893378 (column 9241421688590303745 c) r = column 6826055205333893378 c r) c)
  exact Check.nil

theorem recover_case_4 (K : Subgroup G) (h : ∀ j, recoveryLetter 4 j ∈ K) :
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
