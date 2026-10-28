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

def recoveryLabel1 : Fin 4 → ℕ := ![9241422240497803929, 9241422240506192569, 9241422240506225401, 16527717046453338881]

private theorem conjugator_matrix : HasMatrix (conjugator 1).val 73468327961181920 := by
  apply Check.hasMatrix derivedLetter_matrix
  refine Check.cons (b := 288587807843409470) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 4665733663881429251 (column 288587807843409470 c) r = column 73468327961181920 c r) c)
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

private theorem chosen_matrix : HasMatrix (chosen 1) 9241422240506192569 := by
  apply hasMatrix_of_columns
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    (chosen 1).val (basisVector c) r = column 9241422240506192569 c r) c)

private theorem inverse_matrix : HasMatrix (conjugator 1).val⁻¹ 539440644364476544 := by
  apply conjugator_matrix.inv
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 73468327961181920 (column 539440644364476544 c) r = basisVector (F := ZMod 2) c r) c)

private theorem product_matrix : HasMatrix ((conjugator 1).val * chosen 1) 13366010167846428384 := by
  apply conjugator_matrix.mul chosen_matrix
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 73468327961181920 (column 9241422240506192569 c) r = column 13366010167846428384 c r) c)

private theorem supplement_matrix : HasMatrix (supplement 1) 16527717046453338881 := by
  apply product_matrix.mul inverse_matrix
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 13366010167846428384 (column 539440644364476544 c) r = column 16527717046453338881 c r) c)

private theorem recovery_matrix (j : Fin 4) : HasMatrix (recoveryLetter 1 j) (recoveryLabel1 j) := by
  fin_cases j
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 1 0).val (basisVector c) r = column 9241422240497803929 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 1 1).val (basisVector c) r = column 9241422240506192569 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 1 2).val (basisVector c) r = column 9241422240506225401 c r) c)
  · exact supplement_matrix

private theorem recover_c : word (recoveryLetter 1) [0] = basicLetter 0 := by
  apply HasMatrix.eq (n := 9241422240497803929) ?_ (basicLetter_matrix 0)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240497803929 (column 9241421688590303745 c) r = column 9241422240497803929 c r) c)
  exact Check.nil

private theorem recover_e : word (recoveryLetter 1) [3, 0, 2, 3, 1, 2, 3, 0, 2, 3] = basicLetter 1 := by
  apply HasMatrix.eq (n := 9241492057334482433) ?_ (basicLetter_matrix 1)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 11914971081569797889) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 11914971081569797889 c) r = column 9241492057334482433 c r) c)
  refine Check.cons (b := 11914971793013570748) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240497803929 (column 11914971793013570748 c) r = column 11914971081569797889 c r) c)
  refine Check.cons (b := 11914971081579995680) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506225401 (column 11914971081579995680 c) r = column 11914971793013570748 c r) c)
  refine Check.cons (b := 306316311779115552) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 306316311779115552 c) r = column 11914971081579995680 c r) c)
  refine Check.cons (b := 306316329030566781) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 306316329030566781 c) r = column 306316311779115552 c r) c)
  refine Check.cons (b := 306316311779116640) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506225401 (column 306316311779116640 c) r = column 306316329030566781 c r) c)
  refine Check.cons (b := 16527717046467749472) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 16527717046467749472 c) r = column 306316311779116640 c r) c)
  refine Check.cons (b := 16527717999361055133) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240497803929 (column 16527717999361055133 c) r = column 16527717046467749472 c r) c)
  refine Check.cons (b := 16527717046453338881) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506225401 (column 16527717046453338881 c) r = column 16527717999361055133 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 9241421688590303745 c) r = column 16527717046453338881 c r) c)
  exact Check.nil

private theorem recover_f : word (recoveryLetter 1) [0, 2, 3, 0, 3, 2, 3, 2, 3, 0, 3] = basicLetter 2 := by
  apply HasMatrix.eq (n := 9277450623588762115) ?_ (basicLetter_matrix 2)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9277451175504650907) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240497803929 (column 9277451175504650907 c) r = column 9277450623588762115 c r) c)
  refine Check.cons (b := 9277450623597183715) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506225401 (column 9277450623597183715 c) r = column 9277451175504650907 c r) c)
  refine Check.cons (b := 4604619517700563427) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 4604619517700563427 c) r = column 9277450623597183715 c r) c)
  refine Check.cons (b := 4604619668349093060) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240497803929 (column 4604619668349093060 c) r = column 4604619517700563427 c r) c)
  refine Check.cons (b := 4738635682853765316) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 4738635682853765316 c) r = column 4604619668349093060 c r) c)
  refine Check.cons (b := 4738635963125663066) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506225401 (column 4738635963125663066 c) r = column 4738635682853765316 c r) c)
  refine Check.cons (b := 2531511962670817114) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 2531511962670817114 c) r = column 4738635963125663066 c r) c)
  refine Check.cons (b := 2531511811759915260) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506225401 (column 2531511811759915260 c) r = column 2531511962670817114 c r) c)
  refine Check.cons (b := 16527717999354526972) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 16527717999354526972 c) r = column 2531511811759915260 c r) c)
  refine Check.cons (b := 16527717046453338881) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240497803929 (column 16527717046453338881 c) r = column 16527717999354526972 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 9241421688590303745 c) r = column 16527717046453338881 c r) c)
  exact Check.nil

private theorem recover_r : word (recoveryLetter 1) [3, 0, 3, 1, 3, 0, 1, 3, 1, 3, 0, 3] = basicLetter 3 := by
  apply HasMatrix.eq (n := 9232449673707521025) ?_ (basicLetter_matrix 3)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 16374629843494700289) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 16374629843494700289 c) r = column 9232449673707521025 c r) c)
  refine Check.cons (b := 16374630805017549562) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240497803929 (column 16374630805017549562 c) r = column 16374629843494700289 c r) c)
  refine Check.cons (b := 4990510185031639290) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 4990510185031639290 c) r = column 16374630805017549562 c r) c)
  refine Check.cons (b := 4990510482541738621) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 4990510482541738621 c) r = column 4990510185031639290 c r) c)
  refine Check.cons (b := 6980586493932603261) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 6980586493932603261 c) r = column 4990510482541738621 c r) c)
  refine Check.cons (b := 6980586079998836997) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240497803929 (column 6980586079998836997 c) r = column 6980586493932603261 c r) c)
  refine Check.cons (b := 6980586493934700411) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 6980586493934700411 c) r = column 6980586079998836997 c r) c)
  refine Check.cons (b := 2531511962670824571) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 2531511962670824571 c) r = column 6980586493934700411 c r) c)
  refine Check.cons (b := 2531511811759915260) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 2531511811759915260 c) r = column 2531511962670824571 c r) c)
  refine Check.cons (b := 16527717999354526972) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 16527717999354526972 c) r = column 2531511811759915260 c r) c)
  refine Check.cons (b := 16527717046453338881) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240497803929 (column 16527717046453338881 c) r = column 16527717999354526972 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 9241421688590303745 c) r = column 16527717046453338881 c r) c)
  exact Check.nil

private theorem recover_s : word (recoveryLetter 1) [0, 1, 2, 3, 1, 2, 3, 1, 2, 3, 0] = basicLetter 4 := by
  apply HasMatrix.eq (n := 4647719248123134210) ?_ (basicLetter_matrix 4)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 4647719524083172698) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240497803929 (column 4647719524083172698 c) r = column 4647719248123134210 c r) c)
  refine Check.cons (b := 4647719248127328518) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 4647719248127328518 c) r = column 4647719524083172698 c r) c)
  refine Check.cons (b := 4647719524083189210) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506225401 (column 4647719524083189210 c) r = column 4647719248127328518 c r) c)
  refine Check.cons (b := 13726166468276166618) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 13726166468276166618 c) r = column 4647719524083189210 c r) c)
  refine Check.cons (b := 13726165804003212383) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 13726165804003212383 c) r = column 13726166468276166618 c r) c)
  refine Check.cons (b := 13726166468276134311) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506225401 (column 13726166468276134311 c) r = column 13726165804003212383 c r) c)
  refine Check.cons (b := 4413184548253042343) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 4413184548253042343 c) r = column 13726166468276134311 c r) c)
  refine Check.cons (b := 4413184363116511557) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506192569 (column 4413184363116511557 c) r = column 4413184548253042343 c r) c)
  refine Check.cons (b := 4413184548253055897) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240506225401 (column 4413184548253055897 c) r = column 4413184363116511557 c r) c)
  refine Check.cons (b := 9241422240497803929) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16527717046453338881 (column 9241422240497803929 c) r = column 4413184548253055897 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241422240497803929 (column 9241421688590303745 c) r = column 9241422240497803929 c r) c)
  exact Check.nil

theorem recover_case_1 (K : Subgroup G) (h : ∀ j, recoveryLetter 1 j ∈ K) :
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
