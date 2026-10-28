module

public import Theory.SpecificGroups.PSL3Three.FiniteModel
public import Theory.GroupTheory.WordSubgroup
public import Mathlib.Algebra.Field.ZMod

/-!
# A small generating alphabet for SL₃(3)

The coordinate three-cycle and the elementary matrix `1 + E₀₁`, together
with their inverses, generate SL₃(3). We certify words for all transvections
and the two-coordinate diagonal matrices over `ZMod 3`, then apply matrix
elimination (`diagonal_transvection_induction'`). Only these short word
equations require finite checking; no enumeration of all 5,616 matrices is
used to prove generation.

Source: elementary row reduction, as formalized in Mathlib's special linear
group induction theorem. This supplies the ambient alphabet for the subgroup
extension certificates of GLS III, Theorem 6.5.3.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration

open Theory.GroupTheory

/-- A coordinate cycle, an elementary matrix, and their inverses. -/
@[expose] public def ambientGenerator : Fin 4 → SL :=
  ![⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩,
    ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩,
    ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide⟩,
    ⟨!![1, 2, 0; 0, 1, 0; 0, 0, 1], by decide⟩]

@[expose] public def ambientInverse : Fin 4 → Fin 4 := ![2, 3, 0, 1]

public theorem ambientGenerator_inv : ∀ i,
    ambientGenerator (ambientInverse i) = (ambientGenerator i)⁻¹ := by decide

/-- Words expressing every transvection; diagonal index pairs are unused. -/
@[expose] public def transvectionWord : Fin 3 → Fin 3 → ZMod 3 → List (Fin 4) :=
  ![![![[], [], []], ![[], [1], [3]], ![[], [0, 1, 2, 3, 0, 3, 2, 1], [0, 1, 2, 1, 0, 3, 2, 3]]], ![![[], [0, 1, 0, 1, 2, 3, 0, 3, 0], [0, 1, 0, 3, 2, 3, 0, 1, 0]], ![[], [], []], ![[], [0, 1, 2], [0, 3, 2]]], ![![[], [2, 1, 0], [2, 3, 0]], ![[], [1, 2, 3, 0, 3, 2, 1, 0], [1, 2, 1, 0, 3, 2, 3, 0]], ![[], [], []]]]

/-- Words expressing every determinant-one two-coordinate diagonal matrix;
zero coefficients and equal index pairs are unused. -/
@[expose] public def diagonalWord : Fin 3 → Fin 3 → ZMod 3 → List (Fin 4) :=
  ![![![[], [], []], ![[], [], [0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 2, 3, 2, 3]], ![[], [], [0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 2, 3, 2, 3, 0, 3]]], ![![[], [], [0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 2, 3, 2, 3]], ![[], [], []], ![[], [], [0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3]]], ![![[], [], [0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 2, 3, 2, 3, 0, 3]], ![[], [], [0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3]], ![[], [], []]]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem transvectionWord_eval : ∀ (i j : Fin 3) (h : i ≠ j) (a : ZMod 3),
    evalWord ambientGenerator (transvectionWord i j a) =
      SpecialLinearGroup.transvection h a := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem diagonalWord_eval : ∀ (i j : Fin 3) (h : i ≠ j) (a : ZMod 3) (ha : a ≠ 0),
    evalWord ambientGenerator (diagonalWord i j a) =
      SpecialLinearGroup.diag2n h a ha := by
  have hinv : ∀ c : ZMod 3, c⁻¹ = c := by
    intro c
    by_cases hc : c = 0
    · simp [hc]
    · exact inv_eq_of_mul_eq_one_left
        ((by decide : ∀ c : ZMod 3, c ≠ 0 → c * c = 1) c hc)
  have checked : ∀ (i j : Fin 3) (a : ZMod 3), i ≠ j → a ≠ 0 →
      (evalWord ambientGenerator (diagonalWord i j a)).val =
        diagonal (fun k => if k = i then a else if k = j then a else 1) := by decide
  intro i j h a ha
  apply Subtype.ext
  simpa only [SpecialLinearGroup.diag2n_coe, hinv] using checked i j a h ha

set_option maxHeartbeats 2000000 in
/-- The ambient alphabet generates the actual determinant-one matrix group. -/
public theorem ambient_wordSubgroup_eq_top :
    wordSubgroup ambientGenerator ambientInverse ambientGenerator_inv = ⊤ := by
  apply top_unique
  intro g _
  apply SpecialLinearGroup.diagonal_transvection_induction'
    (fun x => x ∈ wordSubgroup ambientGenerator ambientInverse ambientGenerator_inv) g
  · intro i j h a ha
    exact ⟨diagonalWord i j a, diagonalWord_eval i j h a ha⟩
  · intro i j h a
    exact ⟨transvectionWord i j a, transvectionWord_eval i j h a⟩
  · intro a b ha hb
    exact (wordSubgroup ambientGenerator ambientInverse ambientGenerator_inv).mul_mem ha hb

end Matrix.PSL3Three.CertifiedEnumeration
