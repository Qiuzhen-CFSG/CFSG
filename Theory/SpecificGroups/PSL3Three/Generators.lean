module

public import Theory.SpecificGroups.PSL3Three.Basic
public import Mathlib.Algebra.Field.ZMod
public import Theory.GroupTheory.SubgroupEnumeration

/-!
# Small generators for SL₃(3)

A cyclic coordinate permutation and one elementary transvection generate the
special linear group. Short words give the other elementary transvections;
elimination reduces arbitrary matrices to these and two-entry diagonal matrices.
The diagonal matrices are products of four transvections.

This is the elementary-matrix generation argument used for the concrete
subgroup certificates in GLS III, Theorem 6.5.3(a–c).
-/

namespace Matrix.PSL3Three
open SpecialLinearGroup Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- A coordinate cycle, an elementary transvection, and their inverses. -/
@[expose] public def ambientGenerators : Fin 4 → SL :=
  ![⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩,
    ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩,
    ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide⟩,
    ⟨!![1, 2, 0; 0, 1, 0; 0, 0, 1], by decide⟩]

@[expose] public def ambientInverse : Fin 4 → Fin 4 := ![2, 3, 0, 1]

public theorem ambientGenerators_inverse (i : Fin 4) :
    ambientGenerators (ambientInverse i) = (ambientGenerators i)⁻¹ := by
  apply Subtype.ext
  revert i
  decide

private def elementary (i j : Fin 3) (c : ZMod 3) : SL :=
  if h : i ≠ j then SpecialLinearGroup.transvection h c else 1

private def elementaryWords : Fin 3 → Fin 3 → List (Fin 4) :=
  ![![[], [1], [0, 1, 2, 3, 0, 3, 2, 1]],
    ![[0, 1, 0, 1, 2, 3, 0, 3, 0], [], [0, 1, 2]],
    ![[2, 1, 0], [1, 2, 3, 0, 3, 2, 1, 0], []]]

private theorem elementaryWords_eval (i j : Fin 3) :
    evalWord ambientGenerators (elementaryWords i j) = elementary i j 1 := by
  apply Subtype.ext
  revert i j
  decide

private theorem elementary_coeff : ∀ i j : Fin 3, ∀ c : ZMod 3,
    elementary i j c = (elementary i j 1) ^ c.val := by
  decide

private theorem diag_matrix : ∀ i j : Fin 3, ∀ c : ZMod 3, i ≠ j → c ≠ 0 →
    Matrix.diagonal (fun r => if r = i then c else if r = j then c⁻¹ else 1) =
    ((elementary i j (c - 1) * elementary j i 1) *
      elementary i j (c⁻¹ - 1) * elementary j i (-c)).val := by
  have hinv : ∀ c : ZMod 3, c⁻¹ = c := by
    intro c
    by_cases hc : c = 0
    · simp [hc]
    · exact inv_eq_of_mul_eq_one_left ((by decide : ∀ c : ZMod 3, c ≠ 0 → c * c = 1) c hc)
  simp only [hinv]
  decide

/-- Checking the four specified generators suffices for equality with SL₃(3). -/
public theorem eq_top_of_ambientGenerators_mem (H : Subgroup SL)
    (hgen : ∀ i, ambientGenerators i ∈ H) : H = ⊤ := by
  have hel (i j : Fin 3) (c : ZMod 3) : elementary i j c ∈ H := by
    rw [elementary_coeff, ← elementaryWords_eval]
    exact H.pow_mem (evalWord_mem _ H hgen _) _
  have ht (i j : Fin 3) (hij : i ≠ j) (c : ZMod 3) : SpecialLinearGroup.transvection hij c ∈ H := by
    simpa [elementary, hij] using hel i j c
  apply top_unique
  intro a _
  apply diagonal_transvection_induction' (fun x => x ∈ H) a ?_ ht (fun _ _ => H.mul_mem)
  intro i j hij c hc
  have hd : diag2n hij c hc =
      ((SpecialLinearGroup.transvection hij (c - 1) * SpecialLinearGroup.transvection hij.symm 1) *
        SpecialLinearGroup.transvection hij (c⁻¹ - 1) * SpecialLinearGroup.transvection hij.symm (-c)) := by
    apply Subtype.ext
    simpa [diag2n_coe, elementary, hij, hij.symm] using diag_matrix i j c hij hc
  rw [hd]
  exact H.mul_mem (H.mul_mem (H.mul_mem (ht _ _ _ _) (ht _ _ _ _))
    (ht _ _ _ _)) (ht _ _ _ _)

public theorem ambient_wordSubgroup_eq_top :
    wordSubgroup ambientGenerators ambientInverse ambientGenerators_inverse = ⊤ := by
  apply eq_top_of_ambientGenerators_mem
  intro i
  exact ⟨[i], by simp [evalWord]⟩

end Matrix.PSL3Three
