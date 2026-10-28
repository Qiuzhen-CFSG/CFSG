module

public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Data
/-!
# Kernel evaluator for the literal alternating quartic

A four-by-four determinant in characteristic two is the sum of six products of
two-by-two minors. We prove this polynomial formula from the determinant
expansion, and prove that evaluation using short rows of quadruples equals the
actual form from `Basic.lean` on every tuple of vectors. The short rows copy the
same lexicographic quadruples; their equality is checked in the kernel.
-/

@[expose] public section
namespace BinaryQuarticMathieu.RankRecognition.Orbits

private def det3 (m : Matrix (Fin 3) (Fin 3) F) : F :=
  m 0 0 * m 1 1 * m 2 2 - m 0 0 * m 1 2 * m 2 1
  - m 0 1 * m 1 0 * m 2 2 + m 0 1 * m 1 2 * m 2 0
  + m 0 2 * m 1 0 * m 2 1 - m 0 2 * m 1 1 * m 2 0

private def det4 (m : Matrix (Fin 4) (Fin 4) F) : F :=
  ∑ j : Fin 4, (-1) ^ j.val * m 0 j * det3 (m.submatrix Fin.succ j.succAbove)

private theorem det4_eq (m : Matrix (Fin 4) (Fin 4) F) : det4 m = m.det := by
  rw [Matrix.det_succ_row_zero]
  simp only [det4, det3, Matrix.det_fin_three]

def det4Fast (m : Matrix (Fin 4) (Fin 4) F) : F :=
  (m 0 0 * m 1 1 + m 0 1 * m 1 0) * (m 2 2 * m 3 3 + m 2 3 * m 3 2) +
  (m 0 0 * m 1 2 + m 0 2 * m 1 0) * (m 2 1 * m 3 3 + m 2 3 * m 3 1) +
  (m 0 0 * m 1 3 + m 0 3 * m 1 0) * (m 2 1 * m 3 2 + m 2 2 * m 3 1) +
  (m 0 1 * m 1 2 + m 0 2 * m 1 1) * (m 2 0 * m 3 3 + m 2 3 * m 3 0) +
  (m 0 1 * m 1 3 + m 0 3 * m 1 1) * (m 2 0 * m 3 2 + m 2 2 * m 3 0) +
  (m 0 2 * m 1 3 + m 0 3 * m 1 2) * (m 2 0 * m 3 1 + m 2 1 * m 3 0)

theorem det4Fast_eq (m : Matrix (Fin 4) (Fin 4) F) : det4Fast m = m.det := by
  have hn : ∀ x : F, -x = x := by decide +kernel
  rw [← det4_eq]
  simp [det4, det3, Fin.sum_univ_succ, Matrix.submatrix, sub_eq_add_neg, hn,
    det4Fast, Fin.succAbove]
  ring

def quadRows : Array (Array (Fin 4 → Fin 10)) := #[
  #[![0, 1, 2, 3], ![0, 1, 2, 4], ![0, 1, 2, 5], ![0, 1, 2, 6], ![0, 1, 2, 7], ![0, 1, 2, 8], ![0, 1, 2, 9], ![0, 1, 3, 4], ![0, 1, 3, 5], ![0, 1, 3, 6], ![0, 1, 3, 7], ![0, 1, 3, 8], ![0, 1, 3, 9], ![0, 1, 4, 5]],
  #[![0, 1, 4, 6], ![0, 1, 4, 7], ![0, 1, 4, 8], ![0, 1, 4, 9], ![0, 1, 5, 6], ![0, 1, 5, 7], ![0, 1, 5, 8], ![0, 1, 5, 9], ![0, 1, 6, 7], ![0, 1, 6, 8], ![0, 1, 6, 9], ![0, 1, 7, 8], ![0, 1, 7, 9], ![0, 1, 8, 9]],
  #[![0, 2, 3, 4], ![0, 2, 3, 5], ![0, 2, 3, 6], ![0, 2, 3, 7], ![0, 2, 3, 8], ![0, 2, 3, 9], ![0, 2, 4, 5], ![0, 2, 4, 6], ![0, 2, 4, 7], ![0, 2, 4, 8], ![0, 2, 4, 9], ![0, 2, 5, 6], ![0, 2, 5, 7], ![0, 2, 5, 8]],
  #[![0, 2, 5, 9], ![0, 2, 6, 7], ![0, 2, 6, 8], ![0, 2, 6, 9], ![0, 2, 7, 8], ![0, 2, 7, 9], ![0, 2, 8, 9], ![0, 3, 4, 5], ![0, 3, 4, 6], ![0, 3, 4, 7], ![0, 3, 4, 8], ![0, 3, 4, 9], ![0, 3, 5, 6], ![0, 3, 5, 7]],
  #[![0, 3, 5, 8], ![0, 3, 5, 9], ![0, 3, 6, 7], ![0, 3, 6, 8], ![0, 3, 6, 9], ![0, 3, 7, 8], ![0, 3, 7, 9], ![0, 3, 8, 9], ![0, 4, 5, 6], ![0, 4, 5, 7], ![0, 4, 5, 8], ![0, 4, 5, 9], ![0, 4, 6, 7], ![0, 4, 6, 8]],
  #[![0, 4, 6, 9], ![0, 4, 7, 8], ![0, 4, 7, 9], ![0, 4, 8, 9], ![0, 5, 6, 7], ![0, 5, 6, 8], ![0, 5, 6, 9], ![0, 5, 7, 8], ![0, 5, 7, 9], ![0, 5, 8, 9], ![0, 6, 7, 8], ![0, 6, 7, 9], ![0, 6, 8, 9], ![0, 7, 8, 9]],
  #[![1, 2, 3, 4], ![1, 2, 3, 5], ![1, 2, 3, 6], ![1, 2, 3, 7], ![1, 2, 3, 8], ![1, 2, 3, 9], ![1, 2, 4, 5], ![1, 2, 4, 6], ![1, 2, 4, 7], ![1, 2, 4, 8], ![1, 2, 4, 9], ![1, 2, 5, 6], ![1, 2, 5, 7], ![1, 2, 5, 8]],
  #[![1, 2, 5, 9], ![1, 2, 6, 7], ![1, 2, 6, 8], ![1, 2, 6, 9], ![1, 2, 7, 8], ![1, 2, 7, 9], ![1, 2, 8, 9], ![1, 3, 4, 5], ![1, 3, 4, 6], ![1, 3, 4, 7], ![1, 3, 4, 8], ![1, 3, 4, 9], ![1, 3, 5, 6], ![1, 3, 5, 7]],
  #[![1, 3, 5, 8], ![1, 3, 5, 9], ![1, 3, 6, 7], ![1, 3, 6, 8], ![1, 3, 6, 9], ![1, 3, 7, 8], ![1, 3, 7, 9], ![1, 3, 8, 9], ![1, 4, 5, 6], ![1, 4, 5, 7], ![1, 4, 5, 8], ![1, 4, 5, 9], ![1, 4, 6, 7], ![1, 4, 6, 8]],
  #[![1, 4, 6, 9], ![1, 4, 7, 8], ![1, 4, 7, 9], ![1, 4, 8, 9], ![1, 5, 6, 7], ![1, 5, 6, 8], ![1, 5, 6, 9], ![1, 5, 7, 8], ![1, 5, 7, 9], ![1, 5, 8, 9], ![1, 6, 7, 8], ![1, 6, 7, 9], ![1, 6, 8, 9], ![1, 7, 8, 9]],
  #[![2, 3, 4, 5], ![2, 3, 4, 6], ![2, 3, 4, 7], ![2, 3, 4, 8], ![2, 3, 4, 9], ![2, 3, 5, 6], ![2, 3, 5, 7], ![2, 3, 5, 8], ![2, 3, 5, 9], ![2, 3, 6, 7], ![2, 3, 6, 8], ![2, 3, 6, 9], ![2, 3, 7, 8], ![2, 3, 7, 9]],
  #[![2, 3, 8, 9], ![2, 4, 5, 6], ![2, 4, 5, 7], ![2, 4, 5, 8], ![2, 4, 5, 9], ![2, 4, 6, 7], ![2, 4, 6, 8], ![2, 4, 6, 9], ![2, 4, 7, 8], ![2, 4, 7, 9], ![2, 4, 8, 9], ![2, 5, 6, 7], ![2, 5, 6, 8], ![2, 5, 6, 9]],
  #[![2, 5, 7, 8], ![2, 5, 7, 9], ![2, 5, 8, 9], ![2, 6, 7, 8], ![2, 6, 7, 9], ![2, 6, 8, 9], ![2, 7, 8, 9], ![3, 4, 5, 6], ![3, 4, 5, 7], ![3, 4, 5, 8], ![3, 4, 5, 9], ![3, 4, 6, 7], ![3, 4, 6, 8], ![3, 4, 6, 9]],
  #[![3, 4, 7, 8], ![3, 4, 7, 9], ![3, 4, 8, 9], ![3, 5, 6, 7], ![3, 5, 6, 8], ![3, 5, 6, 9], ![3, 5, 7, 8], ![3, 5, 7, 9], ![3, 5, 8, 9], ![3, 6, 7, 8], ![3, 6, 7, 9], ![3, 6, 8, 9], ![3, 7, 8, 9], ![4, 5, 6, 7]],
  #[![4, 5, 6, 8], ![4, 5, 6, 9], ![4, 5, 7, 8], ![4, 5, 7, 9], ![4, 5, 8, 9], ![4, 6, 7, 8], ![4, 6, 7, 9], ![4, 6, 8, 9], ![4, 7, 8, 9], ![5, 6, 7, 8], ![5, 6, 7, 9], ![5, 6, 8, 9], ![5, 7, 8, 9], ![6, 7, 8, 9]]
]
def fastQuad (i : Fin 210) : Fin 4 → Fin 10 :=
  (quadRows[i.val / 14]!).getD (i.val % 14) ![0,1,2,3]

set_option maxRecDepth 4096 in
theorem fastQuad_eq : ∀ i, fastQuad i = quadruple i := by decide +kernel

def evalQuartic (v : Fin 4 → U) : F :=
  ∑ i : Fin 210, if coefficientWord.testBit i.val then
    det4Fast (fun r c => v r (fastQuad i c)) else 0

theorem form_sum_apply {ι : Type*} (s : Finset ι) (f : ι → Form) (v : Fin 4 → U) :
    (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v := by
  exact map_sum (show Form →+ F from
    { toFun := fun Q => Q v, map_zero' := rfl, map_add' := fun _ _ => rfl }) f s

theorem evalQuartic_eq (v : Fin 4 → U) : evalQuartic v = quartic v := by
  simp only [evalQuartic, fastQuad_eq]
  unfold quartic
  rw [form_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : coefficientWord.testBit i.val = true
  · rw [if_pos h, if_pos h]
    exact det4Fast_eq _
  · rw [if_neg h, if_neg h]
    rfl

end BinaryQuarticMathieu.RankRecognition.Orbits
