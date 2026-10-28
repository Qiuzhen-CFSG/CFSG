module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# A dimension-sized family of binary transvection generators

Adjacent elementary matrices, together with the matrix from the last
coordinate to the first, generate the binary special linear group. The
three-index commutator first supplies all increasing roots and then every
remaining root. This retains a family indexed by exactly the dimension.

This is the elementary generation fact used in Aschbacher--Smith 12.7.18,
printed p.845, to bound the codimension of a common fixed space.
-/

public section

open Subgroup
open scoped commutatorElement
namespace BinaryLinear
namespace CyclicTransvectionGeneration

private theorem chain_mem {n : ℕ}
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))
    {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h₁ : Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2) ∈ H)
    (h₂ : Matrix.SpecialLinearGroup.transvection hjk (1 : ZMod 2) ∈ H) :
    Matrix.SpecialLinearGroup.transvection hik (1 : ZMod 2) ∈ H := by
  have he := Atlas.elementary_commutator hik hij hjk (1 : ZMod 2) 1
  rw [one_mul] at he
  rw [← he, commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem h₁ h₂) (H.inv_mem h₁)) (H.inv_mem h₂)

private theorem eq_top_of_cycle_roots {n : ℕ} (hn : 1 ≤ n)
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) (ZMod 2)))
    (hadj : ∀ i : Fin n,
      Matrix.SpecialLinearGroup.transvection
        (show i.castSucc ≠ i.succ by simp [Fin.ext_iff]) (1 : ZMod 2) ∈ H)
    (hwrap : Matrix.SpecialLinearGroup.transvection
      (show Fin.last n ≠ (0 : Fin (n + 1)) by simp [Fin.ext_iff]; omega)
      (1 : ZMod 2) ∈ H) : H = ⊤ := by
  have hup (i j : Fin (n + 1)) (hij : i < j) :
      Matrix.SpecialLinearGroup.transvection hij.ne (1 : ZMod 2) ∈ H := by
    induction j using Fin.induction with
    | zero => exact (Fin.not_lt_zero i hij).elim
    | succ k ih =>
      obtain he | hlt := (Fin.le_castSucc_iff.mpr hij).eq_or_lt
      · subst i
        exact hadj k
      · exact chain_mem H hlt.ne (by simp [Fin.ext_iff]) hij.ne (ih hlt) (hadj k)
  have hlast (j : Fin (n + 1)) (hj : j ≠ Fin.last n) :
      Matrix.SpecialLinearGroup.transvection hj.symm (1 : ZMod 2) ∈ H := by
    by_cases hj0 : j = 0
    · subst j
      exact hwrap
    · exact chain_mem H (by simp [Fin.ext_iff]; omega) (Ne.symm hj0) hj.symm
        hwrap (hup 0 j (Fin.pos_iff_ne_zero.mpr hj0))
  have hroot (i j : Fin (n + 1)) (hij : i ≠ j) :
      Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2) ∈ H := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hup i j hlt
    · by_cases hi : i = Fin.last n
      · subst i
        exact hlast j hij.symm
      · have hj : j ≠ Fin.last n := by
          intro he
          subst j
          exact (not_lt_of_ge (Fin.le_last i)) hgt
        exact chain_mem H hi hj.symm hij
          (hup i (Fin.last n) (lt_of_le_of_ne (Fin.le_last i) hi)) (hlast j hj)
  let : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  apply top_unique
  intro g _
  apply Atlas.sl_elementary_induction (fun g => g ∈ H) _ (fun _ _ => H.mul_mem) g
  intro i j hij c
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · simp
  · exact hroot i j hij

/-- The binary special linear group of dimension `n` has a generating family
of `n` nontrivial elementary transvections. -/
theorem exists_transvection_generators (n : ℕ) (hn : 2 ≤ n) :
    ∃ t : Fin n → Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      (∀ i, ∃ j k, ∃ hjk : j ≠ k,
        t i = Matrix.SpecialLinearGroup.transvection hjk (1 : ZMod 2)) ∧
      Subgroup.closure (Set.range t) = ⊤ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let t : Fin (m + 1) → Matrix.SpecialLinearGroup (Fin (m + 1)) (ZMod 2) :=
    Fin.lastCases
      (Matrix.SpecialLinearGroup.transvection
        (show Fin.last m ≠ (0 : Fin (m + 1)) by simp [Fin.ext_iff]; omega)
        (1 : ZMod 2))
      (fun i => Matrix.SpecialLinearGroup.transvection
        (show i.castSucc ≠ i.succ by simp [Fin.ext_iff]) (1 : ZMod 2))
  refine ⟨t, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact ⟨Fin.last m, 0, by simp [Fin.ext_iff]; omega, by simp [t]⟩
    · exact ⟨j.castSucc, j.succ, by simp [Fin.ext_iff], by simp [t]⟩
  · apply eq_top_of_cycle_roots (by omega)
    · intro i
      apply Subgroup.subset_closure
      exact ⟨i.castSucc, by simp [t]⟩
    · apply Subgroup.subset_closure
      exact ⟨Fin.last m, by simp [t]⟩

end CyclicTransvectionGeneration
end BinaryLinear
