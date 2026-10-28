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

def recoveryLabel7 : Fin 4 → ℕ := ![9241421688598692385, 9241562702038719141, 9241562702038751973, 16383882233842565889]

private theorem conjugator_matrix : HasMatrix (conjugator 7).val 153686518596831100 := by
  apply Check.hasMatrix derivedLetter_matrix
  refine Check.cons (b := 2306584123302574855) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 4665733663881429251 (column 2306584123302574855 c) r = column 153686518596831100 c r) c)
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

private theorem chosen_matrix : HasMatrix (chosen 7) 9241562702038719141 := by
  apply hasMatrix_of_columns
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    (chosen 7).val (basisVector c) r = column 9241562702038719141 c r) c)

private theorem inverse_matrix : HasMatrix (conjugator 7).val⁻¹ 8969974947814473760 := by
  apply conjugator_matrix.inv
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 153686518596831100 (column 8969974947814473760 c) r = basisVector (F := ZMod 2) c r) c)

private theorem product_matrix : HasMatrix ((conjugator 7).val * chosen 7) 6555734381712341884 := by
  apply conjugator_matrix.mul chosen_matrix
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 153686518596831100 (column 9241562702038719141 c) r = column 6555734381712341884 c r) c)

private theorem supplement_matrix : HasMatrix (supplement 7) 16383882233842565889 := by
  apply product_matrix.mul inverse_matrix
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 6555734381712341884 (column 8969974947814473760 c) r = column 16383882233842565889 c r) c)

private theorem recovery_matrix (j : Fin 4) : HasMatrix (recoveryLetter 7 j) (recoveryLabel7 j) := by
  fin_cases j
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 7 0).val (basisVector c) r = column 9241421688598692385 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 7 1).val (basisVector c) r = column 9241562702038719141 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 7 2).val (basisVector c) r = column 9241562702038751973 c r) c)
  · exact supplement_matrix

private theorem recover_c : word (recoveryLetter 7) [3, 2, 3, 0, 1, 3, 2, 3] = basicLetter 0 := by
  apply HasMatrix.eq (n := 9241422240497803929) ?_ (basicLetter_matrix 0)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 6604351793224596377) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 6604351793224596377 c) r = column 9241422240497803929 c r) c)
  refine Check.cons (b := 6604253225246154726) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241562702038751973 (column 6604253225246154726 c) r = column 6604351793224596377 c r) c)
  refine Check.cons (b := 4647930906263206374) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 4647930906263206374 c) r = column 6604253225246154726 c r) c)
  refine Check.cons (b := 4647930906259011874) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 4647930906259011874 c) r = column 4647930906263206374 c r) c)
  refine Check.cons (b := 4647859985615692166) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241562702038719141 (column 4647859985615692166 c) r = column 4647930906259011874 c r) c)
  refine Check.cons (b := 16384057276373575558) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 16384057276373575558 c) r = column 4647859985615692166 c r) c)
  refine Check.cons (b := 16383882233842565889) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241562702038751973 (column 16383882233842565889 c) r = column 16384057276373575558 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 9241421688590303745 c) r = column 16383882233842565889 c r) c)
  exact Check.nil

private theorem recover_e : word (recoveryLetter 7) [0, 3, 2, 3, 0, 3, 2, 3, 0] = basicLetter 1 := by
  apply HasMatrix.eq (n := 9241492057334482433) ?_ (basicLetter_matrix 1)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9241492057342871137) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 9241492057342871137 c) r = column 9241492057334482433 c r) c)
  refine Check.cons (b := 14392372541495011169) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 14392372541495011169 c) r = column 9241492057342871137 c r) c)
  refine Check.cons (b := 14392164281319817986) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241562702038751973 (column 14392164281319817986 c) r = column 14392372541495011169 c r) c)
  refine Check.cons (b := 4647719248123134210) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 4647719248123134210 c) r = column 14392164281319817986 c r) c)
  refine Check.cons (b := 4647719248127328518) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 4647719248127328518 c) r = column 4647719248123134210 c r) c)
  refine Check.cons (b := 14123144848284714758) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 14123144848284714758 c) r = column 4647719248127328518 c r) c)
  refine Check.cons (b := 14123216510304723745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241562702038751973 (column 14123216510304723745 c) r = column 14123144848284714758 c r) c)
  refine Check.cons (b := 9241421688598692385) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 9241421688598692385 c) r = column 14123216510304723745 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 9241421688590303745 c) r = column 9241421688598692385 c r) c)
  exact Check.nil

private theorem recover_f : word (recoveryLetter 7) [1, 3, 1, 3, 0, 2, 3, 0, 1, 2, 3, 1, 3] = basicLetter 2 := by
  apply HasMatrix.eq (n := 9277450623588762115) ?_ (basicLetter_matrix 2)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9277592188940507807) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241562702038719141 (column 9277592188940507807 c) r = column 9277450623588762115 c r) c)
  refine Check.cons (b := 11899036428700698015) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 11899036428700698015 c) r = column 9277592188940507807 c r) c)
  refine Check.cons (b := 11898927719343619271) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241562702038719141 (column 11898927719343619271 c) r = column 11899036428700698015 c r) c)
  refine Check.cons (b := 4901210851907845063) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 4901210851907845063 c) r = column 11898927719343619271 c r) c)
  refine Check.cons (b := 4901210851903912798) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 4901210851903912798 c) r = column 4901210851907845063 c r) c)
  refine Check.cons (b := 4901285601451565954) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241562702038751973 (column 4901285601451565954 c) r = column 4901210851903912798 c r) c)
  refine Check.cons (b := 18175516459265122690) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 18175516459265122690 c) r = column 4901285601451565954 c r) c)
  refine Check.cons (b := 18175516459256472037) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 18175516459256472037 c) r = column 18175516459265122690 c r) c)
  refine Check.cons (b := 18175573547366434113) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241562702038719141 (column 18175573547366434113 c) r = column 18175516459256472037 c r) c)
  refine Check.cons (b := 18175516459256487385) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241562702038751973 (column 18175516459256487385 c) r = column 18175573547366434113 c r) c)
  refine Check.cons (b := 16384057276373550297) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 16384057276373550297 c) r = column 18175516459256487385 c r) c)
  refine Check.cons (b := 16383882233842565889) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241562702038719141 (column 16383882233842565889 c) r = column 16384057276373550297 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 9241421688590303745 c) r = column 16383882233842565889 c r) c)
  exact Check.nil

private theorem recover_r : word (recoveryLetter 7) [2, 3, 0, 3, 0, 1, 2, 3, 0, 3, 2] = basicLetter 3 := by
  apply HasMatrix.eq (n := 9232449673707521025) ?_ (basicLetter_matrix 3)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9232590549180136675) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241562702038751973 (column 9232590549180136675 c) r = column 9232449673707521025 c r) c)
  refine Check.cons (b := 4604339142235611107) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 4604339142235611107 c) r = column 9232590549180136675 c r) c)
  refine Check.cons (b := 4604339142235414277) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 4604339142235414277 c) r = column 4604339142235611107 c r) c)
  refine Check.cons (b := 7420242301351057925) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 7420242301351057925 c) r = column 4604339142235414277 c r) c)
  refine Check.cons (b := 7420242301349092090) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 7420242301349092090 c) r = column 7420242301351057925 c r) c)
  refine Check.cons (b := 7420131146909596510) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241562702038719141 (column 7420131146909596510 c) r = column 7420242301349092090 c r) c)
  refine Check.cons (b := 7420242301349084163) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241562702038751973 (column 7420242301349084163 c) r = column 7420131146909596510 c r) c)
  refine Check.cons (b := 6909619201493581571) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 6909619201493581571 c) r = column 7420242301349084163 c r) c)
  refine Check.cons (b := 6909619201495875557) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 6909619201495875557 c) r = column 6909619201493581571 c r) c)
  refine Check.cons (b := 9241562702038751973) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 9241562702038751973 c) r = column 6909619201495875557 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241562702038751973 (column 9241421688590303745 c) r = column 9241562702038751973 c r) c)
  exact Check.nil

private theorem recover_s : word (recoveryLetter 7) [0, 3, 2, 3, 0] = basicLetter 4 := by
  apply HasMatrix.eq (n := 4647719248123134210) ?_ (basicLetter_matrix 4)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 4647719248127328518) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 4647719248127328518 c) r = column 4647719248123134210 c r) c)
  refine Check.cons (b := 14123144848284714758) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 14123144848284714758 c) r = column 4647719248127328518 c r) c)
  refine Check.cons (b := 14123216510304723745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241562702038751973 (column 14123216510304723745 c) r = column 14123144848284714758 c r) c)
  refine Check.cons (b := 9241421688598692385) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 9241421688598692385 c) r = column 14123216510304723745 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 9241421688590303745 c) r = column 9241421688598692385 c r) c)
  exact Check.nil

theorem recover_case_7 (K : Subgroup G) (h : ∀ j, recoveryLetter 7 j ∈ K) :
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
