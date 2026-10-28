module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.CyclicCoverage.Data

/-!
# Kernel-checked Sylow and fusion tables

Every word and multiplication row is checked on all 63 points of the faithful
published action. The first-point images distinguish all 27 rows. The three
central rows commute with every row; all other rows have checked conjugators
from `a*b`. These finite identities are used to construct the actual subgroup
and prove regular-three fusion in `ThreeSylow`.

A representative multiplication row required 54 seconds with nested vectors,
and 9 seconds with packed tables (including contention on the shared host).
The finite checks are elaborated sequentially to bound memory; no native
oracle or additional axiom is used. Source and provenance: `source/README.md`.
-/

set_option Elab.async false
@[expose] public section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.CyclicCoverageCertificate
open G2DerivedPermutationFiltration.VertexCoordinates
def checkFin {n : Nat} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i, h⟩ else true)
theorem allFin {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt, decide_eq_true_eq] using hi
theorem allFin₂ {n m : Nat} (P : Fin n → Fin m → Prop) [∀ i j, Decidable (P i j)]
    (h : checkFin (fun i => checkFin (fun j => decide (P i j))) = true) : ∀ i j, P i j := by
  intro i
  apply allFin
  have hi := allFin (fun i => checkFin (fun j => decide (P i j)) = true) (by
    simpa only [Bool.decide_eq_true] using h)
  exact hi i

theorem generatorPacked_correct : ∀ (j : Fin 2) (k : Fin 63),
    generatorPacked j k = generator 0 j k := by
  apply allFin₂
  decide +kernel

def wordAction : List (Fin 2) → Fin 63 → Fin 63
  | [], k => k
  | j :: w, k => generatorPacked j (wordAction w k)

theorem perm_apply (w : List (Fin 2)) (k : Fin 63) : perm w k = wordAction w k := by
  induction w generalizing k with
  | nil => rfl
  | cons j w ih =>
    change generator 0 j (perm w k) = generatorPacked j (wordAction w k)
    rw [ih, generatorPacked_correct]


private theorem wordsRow00 : ∀ k : Fin 63,
    wordAction (sylowWords 0) k = sylowTable 0 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow00 : ∀ k : Fin 63,
    wordAction (fusionWords 0) k = fusionTable 0 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow00 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 0 (sylowTable j k) = sylowTable (mulTable 0 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow01 : ∀ k : Fin 63,
    wordAction (sylowWords 1) k = sylowTable 1 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow01 : ∀ k : Fin 63,
    wordAction (fusionWords 1) k = fusionTable 1 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow01 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 1 (sylowTable j k) = sylowTable (mulTable 1 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow02 : ∀ k : Fin 63,
    wordAction (sylowWords 2) k = sylowTable 2 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow02 : ∀ k : Fin 63,
    wordAction (fusionWords 2) k = fusionTable 2 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow02 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 2 (sylowTable j k) = sylowTable (mulTable 2 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow03 : ∀ k : Fin 63,
    wordAction (sylowWords 3) k = sylowTable 3 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow03 : ∀ k : Fin 63,
    wordAction (fusionWords 3) k = fusionTable 3 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow03 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 3 (sylowTable j k) = sylowTable (mulTable 3 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow04 : ∀ k : Fin 63,
    wordAction (sylowWords 4) k = sylowTable 4 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow04 : ∀ k : Fin 63,
    wordAction (fusionWords 4) k = fusionTable 4 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow04 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 4 (sylowTable j k) = sylowTable (mulTable 4 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow05 : ∀ k : Fin 63,
    wordAction (sylowWords 5) k = sylowTable 5 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow05 : ∀ k : Fin 63,
    wordAction (fusionWords 5) k = fusionTable 5 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow05 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 5 (sylowTable j k) = sylowTable (mulTable 5 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow06 : ∀ k : Fin 63,
    wordAction (sylowWords 6) k = sylowTable 6 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow06 : ∀ k : Fin 63,
    wordAction (fusionWords 6) k = fusionTable 6 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow06 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 6 (sylowTable j k) = sylowTable (mulTable 6 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow07 : ∀ k : Fin 63,
    wordAction (sylowWords 7) k = sylowTable 7 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow07 : ∀ k : Fin 63,
    wordAction (fusionWords 7) k = fusionTable 7 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow07 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 7 (sylowTable j k) = sylowTable (mulTable 7 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow08 : ∀ k : Fin 63,
    wordAction (sylowWords 8) k = sylowTable 8 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow08 : ∀ k : Fin 63,
    wordAction (fusionWords 8) k = fusionTable 8 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow08 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 8 (sylowTable j k) = sylowTable (mulTable 8 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow09 : ∀ k : Fin 63,
    wordAction (sylowWords 9) k = sylowTable 9 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow09 : ∀ k : Fin 63,
    wordAction (fusionWords 9) k = fusionTable 9 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow09 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 9 (sylowTable j k) = sylowTable (mulTable 9 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow10 : ∀ k : Fin 63,
    wordAction (sylowWords 10) k = sylowTable 10 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow10 : ∀ k : Fin 63,
    wordAction (fusionWords 10) k = fusionTable 10 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow10 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 10 (sylowTable j k) = sylowTable (mulTable 10 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow11 : ∀ k : Fin 63,
    wordAction (sylowWords 11) k = sylowTable 11 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow11 : ∀ k : Fin 63,
    wordAction (fusionWords 11) k = fusionTable 11 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow11 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 11 (sylowTable j k) = sylowTable (mulTable 11 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow12 : ∀ k : Fin 63,
    wordAction (sylowWords 12) k = sylowTable 12 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow12 : ∀ k : Fin 63,
    wordAction (fusionWords 12) k = fusionTable 12 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow12 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 12 (sylowTable j k) = sylowTable (mulTable 12 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow13 : ∀ k : Fin 63,
    wordAction (sylowWords 13) k = sylowTable 13 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow13 : ∀ k : Fin 63,
    wordAction (fusionWords 13) k = fusionTable 13 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow13 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 13 (sylowTable j k) = sylowTable (mulTable 13 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow14 : ∀ k : Fin 63,
    wordAction (sylowWords 14) k = sylowTable 14 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow14 : ∀ k : Fin 63,
    wordAction (fusionWords 14) k = fusionTable 14 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow14 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 14 (sylowTable j k) = sylowTable (mulTable 14 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow15 : ∀ k : Fin 63,
    wordAction (sylowWords 15) k = sylowTable 15 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow15 : ∀ k : Fin 63,
    wordAction (fusionWords 15) k = fusionTable 15 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow15 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 15 (sylowTable j k) = sylowTable (mulTable 15 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow16 : ∀ k : Fin 63,
    wordAction (sylowWords 16) k = sylowTable 16 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow16 : ∀ k : Fin 63,
    wordAction (fusionWords 16) k = fusionTable 16 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow16 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 16 (sylowTable j k) = sylowTable (mulTable 16 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow17 : ∀ k : Fin 63,
    wordAction (sylowWords 17) k = sylowTable 17 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow17 : ∀ k : Fin 63,
    wordAction (fusionWords 17) k = fusionTable 17 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow17 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 17 (sylowTable j k) = sylowTable (mulTable 17 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow18 : ∀ k : Fin 63,
    wordAction (sylowWords 18) k = sylowTable 18 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow18 : ∀ k : Fin 63,
    wordAction (fusionWords 18) k = fusionTable 18 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow18 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 18 (sylowTable j k) = sylowTable (mulTable 18 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow19 : ∀ k : Fin 63,
    wordAction (sylowWords 19) k = sylowTable 19 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow19 : ∀ k : Fin 63,
    wordAction (fusionWords 19) k = fusionTable 19 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow19 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 19 (sylowTable j k) = sylowTable (mulTable 19 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow20 : ∀ k : Fin 63,
    wordAction (sylowWords 20) k = sylowTable 20 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow20 : ∀ k : Fin 63,
    wordAction (fusionWords 20) k = fusionTable 20 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow20 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 20 (sylowTable j k) = sylowTable (mulTable 20 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow21 : ∀ k : Fin 63,
    wordAction (sylowWords 21) k = sylowTable 21 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow21 : ∀ k : Fin 63,
    wordAction (fusionWords 21) k = fusionTable 21 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow21 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 21 (sylowTable j k) = sylowTable (mulTable 21 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow22 : ∀ k : Fin 63,
    wordAction (sylowWords 22) k = sylowTable 22 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow22 : ∀ k : Fin 63,
    wordAction (fusionWords 22) k = fusionTable 22 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow22 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 22 (sylowTable j k) = sylowTable (mulTable 22 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow23 : ∀ k : Fin 63,
    wordAction (sylowWords 23) k = sylowTable 23 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow23 : ∀ k : Fin 63,
    wordAction (fusionWords 23) k = fusionTable 23 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow23 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 23 (sylowTable j k) = sylowTable (mulTable 23 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow24 : ∀ k : Fin 63,
    wordAction (sylowWords 24) k = sylowTable 24 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow24 : ∀ k : Fin 63,
    wordAction (fusionWords 24) k = fusionTable 24 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow24 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 24 (sylowTable j k) = sylowTable (mulTable 24 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow25 : ∀ k : Fin 63,
    wordAction (sylowWords 25) k = sylowTable 25 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow25 : ∀ k : Fin 63,
    wordAction (fusionWords 25) k = fusionTable 25 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow25 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 25 (sylowTable j k) = sylowTable (mulTable 25 j) k := by
  apply allFin₂
  decide +kernel

private theorem wordsRow26 : ∀ k : Fin 63,
    wordAction (sylowWords 26) k = sylowTable 26 k := by
  apply allFin
  decide +kernel
private theorem fusionWordsRow26 : ∀ k : Fin 63,
    wordAction (fusionWords 26) k = fusionTable 26 k := by
  apply allFin
  decide +kernel
private theorem multiplicationRow26 : ∀ (j : Fin 27) (k : Fin 63),
    sylowTable 26 (sylowTable j k) = sylowTable (mulTable 26 j) k := by
  apply allFin₂
  decide +kernel

theorem words_correct (i : Fin 27) (k : Fin 63) :
    perm (sylowWords i) k = sylowTable i k := by
  rw [perm_apply]
  fin_cases i
  · exact wordsRow00 k
  · exact wordsRow01 k
  · exact wordsRow02 k
  · exact wordsRow03 k
  · exact wordsRow04 k
  · exact wordsRow05 k
  · exact wordsRow06 k
  · exact wordsRow07 k
  · exact wordsRow08 k
  · exact wordsRow09 k
  · exact wordsRow10 k
  · exact wordsRow11 k
  · exact wordsRow12 k
  · exact wordsRow13 k
  · exact wordsRow14 k
  · exact wordsRow15 k
  · exact wordsRow16 k
  · exact wordsRow17 k
  · exact wordsRow18 k
  · exact wordsRow19 k
  · exact wordsRow20 k
  · exact wordsRow21 k
  · exact wordsRow22 k
  · exact wordsRow23 k
  · exact wordsRow24 k
  · exact wordsRow25 k
  · exact wordsRow26 k

theorem fusion_words_correct (i : Fin 27) (k : Fin 63) :
    perm (fusionWords i) k = fusionTable i k := by
  rw [perm_apply]
  fin_cases i
  · exact fusionWordsRow00 k
  · exact fusionWordsRow01 k
  · exact fusionWordsRow02 k
  · exact fusionWordsRow03 k
  · exact fusionWordsRow04 k
  · exact fusionWordsRow05 k
  · exact fusionWordsRow06 k
  · exact fusionWordsRow07 k
  · exact fusionWordsRow08 k
  · exact fusionWordsRow09 k
  · exact fusionWordsRow10 k
  · exact fusionWordsRow11 k
  · exact fusionWordsRow12 k
  · exact fusionWordsRow13 k
  · exact fusionWordsRow14 k
  · exact fusionWordsRow15 k
  · exact fusionWordsRow16 k
  · exact fusionWordsRow17 k
  · exact fusionWordsRow18 k
  · exact fusionWordsRow19 k
  · exact fusionWordsRow20 k
  · exact fusionWordsRow21 k
  · exact fusionWordsRow22 k
  · exact fusionWordsRow23 k
  · exact fusionWordsRow24 k
  · exact fusionWordsRow25 k
  · exact fusionWordsRow26 k

theorem multiplication_correct (i j : Fin 27) (k : Fin 63) :
    sylowTable i (sylowTable j k) = sylowTable (mulTable i j) k := by
  fin_cases i
  · exact multiplicationRow00 j k
  · exact multiplicationRow01 j k
  · exact multiplicationRow02 j k
  · exact multiplicationRow03 j k
  · exact multiplicationRow04 j k
  · exact multiplicationRow05 j k
  · exact multiplicationRow06 j k
  · exact multiplicationRow07 j k
  · exact multiplicationRow08 j k
  · exact multiplicationRow09 j k
  · exact multiplicationRow10 j k
  · exact multiplicationRow11 j k
  · exact multiplicationRow12 j k
  · exact multiplicationRow13 j k
  · exact multiplicationRow14 j k
  · exact multiplicationRow15 j k
  · exact multiplicationRow16 j k
  · exact multiplicationRow17 j k
  · exact multiplicationRow18 j k
  · exact multiplicationRow19 j k
  · exact multiplicationRow20 j k
  · exact multiplicationRow21 j k
  · exact multiplicationRow22 j k
  · exact multiplicationRow23 j k
  · exact multiplicationRow24 j k
  · exact multiplicationRow25 j k
  · exact multiplicationRow26 j k

theorem inverse_correct : ∀ i : Fin 27, mulTable i (invTable i) = 0 := by
  apply allFin
  decide +kernel

theorem separation_correct : Function.Injective (fun i : Fin 27 => sylowTable i 0) := by
  apply allFin₂
  decide +kernel

theorem central_correct : ∀ i : Fin 27, (i = 0 ∨ i = 25 ∨ i = 26) →
    ∀ j : Fin 27, mulTable i j = mulTable j i := by
  intro i hi j
  rcases hi with rfl | rfl | rfl
  · exact (by decide +kernel : ∀ j : Fin 27, mulTable 0 j = mulTable j 0) j
  · exact (by decide +kernel : ∀ j : Fin 27, mulTable 25 j = mulTable j 25) j
  · exact (by decide +kernel : ∀ j : Fin 27, mulTable 26 j = mulTable j 26) j

theorem fusion_correct : ∀ i : Fin 27, ¬ (i = 0 ∨ i = 25 ∨ i = 26) →
    ∀ k : Fin 63,
      fusionTable i (generator 0 0 (generator 0 1 k)) = sylowTable i (fusionTable i k) := by
  have h : ∀ (i : Fin 27) (k : Fin 63), ¬ (i = 0 ∨ i = 25 ∨ i = 26) →
      fusionTable i (generatorPacked 0 (generatorPacked 1 k)) =
        sylowTable i (fusionTable i k) := by
    apply allFin₂
    decide +kernel
  intro i hi k
  simpa only [generatorPacked_correct] using h i k hi

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.CyclicCoverageCertificate
