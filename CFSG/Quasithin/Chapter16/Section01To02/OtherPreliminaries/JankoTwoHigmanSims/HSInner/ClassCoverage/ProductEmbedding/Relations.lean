module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.Seed
import Mathlib.Tactic.FinCases

/-!
# Containment and normalization of the fixed HS product subgroups

Short words prove `A ≤ D ≤ H` and `H ≤ N(D)`. Thus normality is relative
to the intended local overgroup, without asserting ambient normality in HS.
These are checked relations among the exact ATLAS words of `Seed`.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3 Table 5.3m.
The discovery script and candidate relation words are retained in `source/`.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding
open Sporadic.LeechRelated.HS Theory.GroupTheory Subgroup
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false

/-- Generators of `H` and their inverses. -/
def hLetter : Fin 4 → Carrier :=
  ![Seed.generator 0, Seed.generator 1, (Seed.generator 0)⁻¹, (Seed.generator 1)⁻¹]

/-- Generators of `D` and their inverses. -/
def dLetter : Fin 4 → Carrier :=
  ![Seed.generator 2, Seed.generator 3, (Seed.generator 2)⁻¹, (Seed.generator 3)⁻¹]

private theorem hLetter_mem (i : Fin 4) : hLetter i ∈ H := by
  fin_cases i
  · exact subset_closure (by simp [hLetter])
  · exact subset_closure (by simp [hLetter])
  · exact H.inv_mem (subset_closure (by simp))
  · exact H.inv_mem (subset_closure (by simp))

private theorem dLetter_mem (i : Fin 4) : dLetter i ∈ D := by
  fin_cases i
  · exact subset_closure (by simp [dLetter])
  · exact subset_closure (by simp [dLetter])
  · exact D.inv_mem (subset_closure (by simp))
  · exact D.inv_mem (subset_closure (by simp))

theorem hWord_mem (w : List (Fin 4)) : evalWord hLetter w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons i w ih => exact H.mul_mem (hLetter_mem i) ih

theorem dWord_mem (w : List (Fin 4)) : evalWord dLetter w ∈ D := by
  induction w with
  | nil => exact D.one_mem
  | cons i w ih => exact D.mul_mem (dLetter_mem i) ih

private def dInHWord : Fin 2 → List (Fin 4) := ![[1, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 0, 0, 1]]
private def aInDWord : Fin 2 → List (Fin 4) := ![[2, 1, 0, 1, 0, 0], [0, 1, 2, 1, 2, 2, 1, 0]]
private def conjugationWord : Fin 4 → Fin 2 → List (Fin 4) :=
  ![![[1, 2, 2, 1, 0, 1, 0], [0, 0, 1, 0, 1, 2, 2, 1, 0]],
    ![[2, 1, 2, 2, 1, 0], [1, 0, 1, 0, 0, 1, 0, 1, 0, 0]],
    ![[0, 1, 0, 0, 1, 2, 1, 2], [0, 1, 2, 2, 1, 0, 1, 0, 0, 1]],
    ![[0, 0, 1, 2, 1, 0, 0], [0, 1, 0, 1, 2, 2, 1, 0, 0]]]

private theorem dInHWord_eq : ∀ i : Fin 2,
    evalWord hLetter (dInHWord i) = ![Seed.generator 2, Seed.generator 3] i := by
  intro i
  apply Sporadic.LeechRelated.HS.inclusion_injective
  apply Equiv.ext
  have h : ∀ i : Fin 2, ∀ x : Fin 100,
      inclusion (evalWord hLetter (dInHWord i)) x =
        inclusion (![Seed.generator 2, Seed.generator 3] i) x := by
    apply Certificate.allFin
    decide +kernel
  exact h i

private theorem aInDWord_eq : ∀ i : Fin 2,
    evalWord dLetter (aInDWord i) = ![Seed.generator 4, Seed.generator 5] i := by
  intro i
  apply Sporadic.LeechRelated.HS.inclusion_injective
  apply Equiv.ext
  have h : ∀ i : Fin 2, ∀ x : Fin 100,
      inclusion (evalWord dLetter (aInDWord i)) x =
        inclusion (![Seed.generator 4, Seed.generator 5] i) x := by
    apply Certificate.allFin
    decide +kernel
  exact h i

/-- The alternating candidate lies in the automorphism-factor candidate. -/
theorem D_le_H : D ≤ H := by
  apply (closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · have hw := hWord_mem (dInHWord 0)
    rw [dInHWord_eq] at hw
    exact hw
  · rw [Set.mem_singleton_iff.mp hx]
    have hw := hWord_mem (dInHWord 1)
    rw [dInHWord_eq] at hw
    exact hw

/-- The degree-six stabilizer candidate lies in the alternating candidate. -/
theorem A_le_D : A ≤ D := by
  apply (closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · have hw := dWord_mem (aInDWord 0)
    rw [aInDWord_eq] at hw
    exact hw
  · rw [Set.mem_singleton_iff.mp hx]
    have hw := dWord_mem (aInDWord 1)
    rw [aInDWord_eq] at hw
    exact hw

private theorem conjugationWord_eq (i : Fin 4) (j : Fin 2) :
    evalWord dLetter (conjugationWord i j) =
      hLetter i * ![Seed.generator 2, Seed.generator 3] j * (hLetter i)⁻¹ := by
  apply Sporadic.LeechRelated.HS.inclusion_injective
  apply Equiv.ext
  have h : ∀ i : Fin 4, ∀ j : Fin 2, ∀ x : Fin 100,
      inclusion (evalWord dLetter (conjugationWord i j)) x =
        inclusion (hLetter i * ![Seed.generator 2, Seed.generator 3] j * (hLetter i)⁻¹) x := by
    apply Certificate.allFin
    decide +kernel
  exact h i j

private theorem hLetter_conj_mem (i : Fin 4) (d : Carrier) (hd : d ∈ D) :
    hLetter i * d * (hLetter i)⁻¹ ∈ D := by
  have h : D ≤ D.comap (MulAut.conj (hLetter i)).toMonoidHom := by
    apply (closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · have hw := dWord_mem (conjugationWord i 0)
      rw [conjugationWord_eq] at hw
      exact hw
    · rw [Set.mem_singleton_iff.mp hx]
      have hw := dWord_mem (conjugationWord i 1)
      rw [conjugationWord_eq] at hw
      exact hw
  exact h hd

/-- Both local generators normalize `D`, in both conjugation directions. -/
theorem H_le_normalizer : H ≤ normalizer (D : Set Carrier) := by
  have hmem (g : Carrier) (i j : Fin 4) (hi : hLetter i = g) (hj : hLetter j = g⁻¹) :
      g ∈ normalizer (D : Set Carrier) := by
    intro d
    constructor
    · intro hd
      change g * d * g⁻¹ ∈ D
      rw [← hi]
      exact hLetter_conj_mem i d hd
    · intro hd
      have h := hLetter_conj_mem j (g * d * g⁻¹) hd
      change d ∈ D
      simpa only [hj, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h
  apply (closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact hmem _ 0 2 rfl rfl
  · rw [Set.mem_singleton_iff.mp hx]
    exact hmem _ 1 3 rfl rfl

/-- Actual relative normality, after restricting `D` to `H`. -/
instance D_normal_in_H : (D.subgroupOf H).Normal :=
  (normal_subgroupOf_iff_le_normalizer D_le_H).mpr H_le_normalizer

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding
