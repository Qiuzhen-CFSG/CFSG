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

def recoveryLabel5 : Fin 4 → ℕ := ![9277591637032991239, 9241421688598692385, 9277591637041412711, 16383882233842565889]

private theorem conjugator_matrix : HasMatrix (conjugator 5).val 307371864506565438 := by
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

private theorem chosen_matrix : HasMatrix (chosen 5) 9277591637033024199 := by
  apply hasMatrix_of_columns
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    (chosen 5).val (basisVector c) r = column 9277591637033024199 c r) c)

private theorem inverse_matrix : HasMatrix (conjugator 5).val⁻¹ 8989391223647117856 := by
  apply conjugator_matrix.inv
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 307371864506565438 (column 8989391223647117856 c) r = basisVector (F := ZMod 2) c r) c)

private theorem product_matrix : HasMatrix ((conjugator 5).val * chosen 5) 8988278634571840830 := by
  apply conjugator_matrix.mul chosen_matrix
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 307371864506565438 (column 9277591637033024199 c) r = column 8988278634571840830 c r) c)

private theorem supplement_matrix : HasMatrix (supplement 5) 16383882233842565889 := by
  apply product_matrix.mul inverse_matrix
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    linear 8988278634571840830 (column 8989391223647117856 c) r = column 16383882233842565889 c r) c)

private theorem recovery_matrix (j : Fin 4) : HasMatrix (recoveryLetter 5 j) (recoveryLabel5 j) := by
  fin_cases j
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 5 0).val (basisVector c) r = column 9277591637032991239 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 5 1).val (basisVector c) r = column 9241421688598692385 c r) c)
  · apply hasMatrix_of_columns
    exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      (recoveryLetter 5 2).val (basisVector c) r = column 9277591637041412711 c r) c)
  · exact supplement_matrix

private theorem recover_c : word (recoveryLetter 5) [1, 3, 0, 1, 3, 0, 3, 0, 2, 3, 1, 3, 0, 3, 0, 3] = basicLetter 0 := by
  apply HasMatrix.eq (n := 9241422240497803929) ?_ (basicLetter_matrix 0)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9241422240506192569) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 9241422240506192569 c) r = column 9241422240497803929 c r) c)
  refine Check.cons (b := 8865298991743343545) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 8865298991743343545 c) r = column 9241422240506192569 c r) c)
  refine Check.cons (b := 8898169137897691743) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 8898169137897691743 c) r = column 8865298991743343545 c r) c)
  refine Check.cons (b := 8898169137898412794) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 8898169137898412794 c) r = column 8898169137897691743 c r) c)
  refine Check.cons (b := 144995012835123450) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 144995012835123450 c) r = column 8898169137898412794 c r) c)
  refine Check.cons (b := 144434119613782887) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 144434119613782887 c) r = column 144995012835123450 c r) c)
  refine Check.cons (b := 15988807324322102375) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 15988807324322102375 c) r = column 144434119613782887 c r) c)
  refine Check.cons (b := 15942314733843882234) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 15942314733843882234 c) r = column 15988807324322102375 c r) c)
  refine Check.cons (b := 15988807324328010019) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637041412711 (column 15988807324328010019 c) r = column 15942314733843882234 c r) c)
  refine Check.cons (b := 11188386305843069475) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 11188386305843069475 c) r = column 15988807324328010019 c r) c)
  refine Check.cons (b := 11188386305832911361) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 11188386305832911361 c) r = column 11188386305843069475 c r) c)
  refine Check.cons (b := 18400085297309483777) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 18400085297309483777 c) r = column 11188386305832911361 c r) c)
  refine Check.cons (b := 18421344742697303303) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 18421344742697303303 c) r = column 18400085297309483777 c r) c)
  refine Check.cons (b := 16410234647272520199) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 16410234647272520199 c) r = column 18421344742697303303 c r) c)
  refine Check.cons (b := 16383882233842565889) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 16383882233842565889 c) r = column 16410234647272520199 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 9241421688590303745 c) r = column 16383882233842565889 c r) c)
  exact Check.nil

private theorem recover_e : word (recoveryLetter 5) [3, 1, 3, 0, 3, 0, 1, 2, 3, 0, 3, 1, 3] = basicLetter 1 := by
  apply HasMatrix.eq (n := 9241492057334482433) ?_ (basicLetter_matrix 1)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 12059366645110736641) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 12059366645110736641 c) r = column 9241492057334482433 c r) c)
  refine Check.cons (b := 12059366645121025915) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 12059366645121025915 c) r = column 12059366645110736641 c r) c)
  refine Check.cons (b := 18058809672568765563) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 18058809672568765563 c) r = column 12059366645121025915 c r) c)
  refine Check.cons (b := 18043458524320317150) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 18043458524320317150 c) r = column 18058809672568765563 c r) c)
  refine Check.cons (b := 4612952966406987998) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 4612952966406987998 c) r = column 18043458524320317150 c r) c)
  refine Check.cons (b := 4631038302820596859) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 4631038302820596859 c) r = column 4612952966406987998 c r) c)
  refine Check.cons (b := 4631038302816402619) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 4631038302816402619 c) r = column 4631038302820596859 c r) c)
  refine Check.cons (b := 4612952966406971610) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637041412711 (column 4612952966406971610 c) r = column 4631038302816402619 c r) c)
  refine Check.cons (b := 13700932676421122778) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 13700932676421122778 c) r = column 4612952966406971610 c r) c)
  refine Check.cons (b := 13735349890951232575) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 13735349890951232575 c) r = column 13700932676421122778 c r) c)
  refine Check.cons (b := 16383882233857311551) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 16383882233857311551 c) r = column 13735349890951232575 c r) c)
  refine Check.cons (b := 16383882233842565889) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 16383882233842565889 c) r = column 16383882233857311551 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 9241421688590303745 c) r = column 16383882233842565889 c r) c)
  exact Check.nil

private theorem recover_f : word (recoveryLetter 5) [2, 3, 0, 1, 3, 0, 3, 0, 3, 0, 1, 2, 3, 0, 3] = basicLetter 2 := by
  apply HasMatrix.eq (n := 9277450623588762115) ?_ (basicLetter_matrix 2)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9241563253937830621) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637041412711 (column 9241563253937830621 c) r = column 9277450623588762115 c r) c)
  refine Check.cons (b := 14392245395090155485) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 14392245395090155485 c) r = column 9241563253937830621 c r) c)
  refine Check.cons (b := 14374436488571814627) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 14374436488571814627 c) r = column 14392245395090155485 c r) c)
  refine Check.cons (b := 14374436488567554722) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 14374436488567554722 c) r = column 14374436488571814627 c r) c)
  refine Check.cons (b := 15726464526903222434) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 15726464526903222434 c) r = column 14374436488567554722 c r) c)
  refine Check.cons (b := 15773148190651361115) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 15773148190651361115 c) r = column 15726464526903222434 c r) c)
  refine Check.cons (b := 13357565771933678683) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 13357565771933678683 c) r = column 15773148190651361115 c r) c)
  refine Check.cons (b := 13395432111601164450) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 13395432111601164450 c) r = column 13357565771933678683 c r) c)
  refine Check.cons (b := 18421344742697304738) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 18421344742697304738 c) r = column 13395432111601164450 c r) c)
  refine Check.cons (b := 18400085297309547611) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 18400085297309547611 c) r = column 18421344742697304738 c r) c)
  refine Check.cons (b := 18400085297325603943) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 18400085297325603943 c) r = column 18400085297309547611 c r) c)
  refine Check.cons (b := 18421344742697303303) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637041412711 (column 18421344742697303303 c) r = column 18400085297325603943 c r) c)
  refine Check.cons (b := 16410234647272520199) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 16410234647272520199 c) r = column 18421344742697303303 c r) c)
  refine Check.cons (b := 16383882233842565889) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 16383882233842565889 c) r = column 16410234647272520199 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 9241421688590303745 c) r = column 16383882233842565889 c r) c)
  exact Check.nil

private theorem recover_r : word (recoveryLetter 5) [2, 3, 0, 2, 3, 0, 3, 0, 3, 0, 2, 3] = basicLetter 3 := by
  apply HasMatrix.eq (n := 9232449673707521025) ?_ (basicLetter_matrix 3)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 9268619622158629991) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637041412711 (column 9268619622158629991 c) r = column 9232449673707521025 c r) c)
  refine Check.cons (b := 8924408736854678375) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 8924408736854678375 c) r = column 9268619622158629991 c r) c)
  refine Check.cons (b := 8908864919412311137) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 8908864919412311137 c) r = column 8924408736854678375 c r) c)
  refine Check.cons (b := 8924408736859480160) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637041412711 (column 8924408736859480160 c) r = column 8908864919412311137 c r) c)
  refine Check.cons (b := 18205731607691034720) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 18205731607691034720 c) r = column 8924408736859480160 c r) c)
  refine Check.cons (b := 18184193990188466022) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 18184193990188466022 c) r = column 18205731607691034720 c r) c)
  refine Check.cons (b := 154004268831971686) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 154004268831971686 c) r = column 18184193990188466022 c r) c)
  refine Check.cons (b := 153439115541905504) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 153439115541905504 c) r = column 154004268831971686 c r) c)
  refine Check.cons (b := 16383882233857368160) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 16383882233857368160 c) r = column 153439115541905504 c r) c)
  refine Check.cons (b := 16410234647274821990) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 16410234647274821990 c) r = column 16383882233857368160 c r) c)
  refine Check.cons (b := 16383882233842565889) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637041412711 (column 16383882233842565889 c) r = column 16410234647274821990 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 9241421688590303745 c) r = column 16383882233842565889 c r) c)
  exact Check.nil

private theorem recover_s : word (recoveryLetter 5) [2, 3, 0, 1, 3, 1, 2, 3, 0, 3, 2] = basicLetter 4 := by
  apply HasMatrix.eq (n := 4647719248123134210) ?_ (basicLetter_matrix 4)
  apply Check.hasMatrix recovery_matrix
  refine Check.cons (b := 4665804584541543847) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637041412711 (column 4665804584541543847 c) r = column 4647719248123134210 c r) c)
  refine Check.cons (b := 13717539700042594983) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 13717539700042594983 c) r = column 4665804584541543847 c r) c)
  refine Check.cons (b := 13754208279165157766) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 13754208279165157766 c) r = column 13717539700042594983 c r) c)
  refine Check.cons (b := 13754208279173415237) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 13754208279173415237 c) r = column 13754208279165157766 c r) c)
  refine Check.cons (b := 11034456876977423429) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 11034456876977423429 c) r = column 13754208279173415237 c r) c)
  refine Check.cons (b := 11034456876967396353) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9241421688598692385 (column 11034456876967396353 c) r = column 11034456876977423429 c r) c)
  refine Check.cons (b := 11077691213496050529) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637041412711 (column 11077691213496050529 c) r = column 11034456876967396353 c r) c)
  refine Check.cons (b := 9062583242045293153) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 9062583242045293153 c) r = column 11077691213496050529 c r) c)
  refine Check.cons (b := 9059481541303573863) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637032991239 (column 9059481541303573863 c) r = column 9062583242045293153 c r) c)
  refine Check.cons (b := 9277591637041412711) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 16383882233842565889 (column 9277591637041412711 c) r = column 9059481541303573863 c r) c)
  refine Check.cons (b := 9241421688590303745) ?_ ?_
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      linear 9277591637041412711 (column 9241421688590303745 c) r = column 9277591637041412711 c r) c)
  exact Check.nil

theorem recover_case_5 (K : Subgroup G) (h : ∀ j, recoveryLetter 5 j ∈ K) :
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
