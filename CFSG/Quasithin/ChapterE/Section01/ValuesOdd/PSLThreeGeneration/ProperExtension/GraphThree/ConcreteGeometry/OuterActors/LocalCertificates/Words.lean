module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.Coordinates.Table
public import Theory.SpecificGroups.PSL3Three.Generators

/-!
# Checked words for the selected PSL₃(3) graph centralizer

Two matrices of the standard Sylow, together with `extra`, generate SL₃(3).
The two displayed chains of matrix products reach the coordinate cycle and
an elementary transvection. Each step is checked by the kernel; induction
along the chains proves subgroup membership without reducing a long product.
The inverse generators then give the existing elementary-matrix generation
criterion. `LocalCertificates` applies this to the literal inner embedding.

Source: Aschbacher–Smith E.1.14(7), printed p.214; Asc82a Lemma 4.11.
The words were found by the parent task's `Scratch/GraphThreeOuter/LocalWords.py`;
the matrices here are independent checked certificates of those diagnostics.
-/

public section
open Subgroup Matrix.PSL3Three
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.LocalCertificates
set_option maxRecDepth 10000

/-- The additional matrix lying in the selected graph centralizer. -/
@[expose] def extra : SL := ⟨!![0,0,2; 2,2,1; 2,0,0], by decide⟩
private def generators : Fin 4 → SL := ![twoElement 1, twoElement 7, twoElement 8, extra]

private theorem mem_last_of_steps {n : ℕ} (H : Subgroup SL)
    (states : Fin (n+1) → SL) (steps : Fin n → Fin 4)
    (hzero : states 0 = 1)
    (hstep : ∀ i, states i.castSucc * generators (steps i) = states i.succ)
    (hgen : ∀ i, generators i ∈ H) : states (Fin.last n) ∈ H := by
  have hm (i : Fin (n+1)) : states i ∈ H := by
    induction i using Fin.induction with
    | zero => rw [hzero]; exact H.one_mem
    | succ i ih => rw [← hstep i]; exact H.mul_mem ih (hgen _)
  exact hm _

private def cycleStates : Fin 13 → SL :=
  ![⟨!![1,0,0; 0,1,0; 0,0,1], by decide⟩,
    ⟨!![2,0,0; 0,1,0; 0,1,2], by decide⟩,
    ⟨!![0,0,1; 2,2,1; 0,2,1], by decide⟩,
    ⟨!![0,1,0; 1,2,2; 0,2,2], by decide⟩,
    ⟨!![2,2,1; 2,1,1; 2,1,2], by decide⟩,
    ⟨!![1,2,2; 1,0,1; 1,1,1], by decide⟩,
    ⟨!![2,1,1; 2,0,2; 1,2,0], by decide⟩,
    ⟨!![1,1,2; 1,2,2; 2,0,2], by decide⟩,
    ⟨!![0,2,0; 2,1,1; 1,0,1], by decide⟩,
    ⟨!![0,0,2; 1,1,2; 2,1,1], by decide⟩,
    ⟨!![1,0,0; 0,2,0; 1,2,2], by decide⟩,
    ⟨!![2,0,0; 0,0,2; 2,2,1], by decide⟩,
    ⟨!![0,0,1; 1,0,0; 0,1,0], by decide⟩]

private def cycleSteps : Fin 12 → Fin 4 :=
  ![2, 3, 1, 3, 1, 3, 0, 3, 0, 3, 0, 3]

private theorem cycleSteps_checked (i : Fin 12) :
    cycleStates i.castSucc * generators (cycleSteps i) = cycleStates i.succ := by
  apply Subtype.ext
  revert i
  decide +kernel

private def transvectionStates : Fin 15 → SL :=
  ![⟨!![1,0,0; 0,1,0; 0,0,1], by decide⟩,
    ⟨!![0,0,2; 2,2,1; 2,0,0], by decide⟩,
    ⟨!![0,2,2; 1,1,0; 1,0,0], by decide⟩,
    ⟨!![2,1,2; 2,2,0; 0,0,2], by decide⟩,
    ⟨!![1,2,0; 1,0,2; 0,2,2], by decide⟩,
    ⟨!![1,1,1; 1,0,2; 2,1,2], by decide⟩,
    ⟨!![2,1,2; 2,2,2; 1,2,0], by decide⟩,
    ⟨!![0,2,2; 2,1,0; 1,1,1], by decide⟩,
    ⟨!![0,2,1; 1,0,1; 2,1,2], by decide⟩,
    ⟨!![0,1,2; 2,0,2; 0,2,2], by decide⟩,
    ⟨!![0,2,0; 1,2,2; 0,2,1], by decide⟩,
    ⟨!![0,2,0; 2,1,1; 0,0,2], by decide⟩,
    ⟨!![1,1,2; 1,2,2; 1,0,0], by decide⟩,
    ⟨!![2,2,0; 2,2,1; 2,0,0], by decide⟩,
    ⟨!![1,1,0; 0,1,0; 0,0,1], by decide⟩]

private def transvectionSteps : Fin 14 → Fin 4 :=
  ![3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 2, 3, 0, 3]

private theorem transvectionSteps_checked (i : Fin 14) :
    transvectionStates i.castSucc * generators (transvectionSteps i) = transvectionStates i.succ := by
  apply Subtype.ext
  revert i
  decide +kernel

/-- The selected two Sylow matrices and the additional centralizer matrix
already generate the whole special linear group. -/
theorem eq_top_of_twoElement_extra_mem (H : Subgroup SL)
    (ha : twoElement 1 ∈ H) (hb : twoElement 8 ∈ H) (hk : extra ∈ H) : H = ⊤ := by
  have hai : twoElement 7 ∈ H := by
    have hi : twoElement 7 = (twoElement 1)⁻¹ := twoElement_inv 1
    rw [hi]
    exact H.inv_mem ha
  have hgen (i : Fin 4) : generators i ∈ H := by
    fin_cases i
    · exact ha
    · exact hai
    · exact hb
    · exact hk
  have hc : ambientGenerators 0 ∈ H :=
    mem_last_of_steps H cycleStates cycleSteps
      (Subtype.ext (by decide +kernel)) cycleSteps_checked hgen
  have ht : ambientGenerators 1 ∈ H :=
    mem_last_of_steps H transvectionStates transvectionSteps
      (Subtype.ext (by decide +kernel)) transvectionSteps_checked hgen
  apply eq_top_of_ambientGenerators_mem
  intro i
  fin_cases i
  · exact hc
  · exact ht
  · change ambientGenerators 2 ∈ H
    have hi : ambientGenerators 2 = (ambientGenerators 0)⁻¹ := ambientGenerators_inverse 0
    rw [hi]
    exact H.inv_mem hc
  · change ambientGenerators 3 ∈ H
    have hi : ambientGenerators 3 = (ambientGenerators 1)⁻¹ := ambientGenerators_inverse 1
    rw [hi]
    exact H.inv_mem ht

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.LocalCertificates
