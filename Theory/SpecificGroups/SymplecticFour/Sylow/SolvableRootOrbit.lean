module

public import Theory.SpecificGroups.SymplecticFour.Sylow.Normalizer
public import Mathlib.GroupTheory.Solvable
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.IsPerfect
import Mathlib.Algebra.CharP.Reduced
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Orthogonal point orbits in solvable unipotent overgroups

Over a finite field of characteristic two with more than two elements, a
solvable subgroup of the actual matrix group Sp₄ containing the standard
unipotent subgroup has its e₀-orbit in e₀-perpendicular.

If the f₀-coordinate of g(e₀) is nonzero, three positive-root row operations
clear its other coordinates. Preservation of the alternating form then shows
that conjugating the full upper long-root group gives the full opposite
long-root group. We explicitly embed SL₂ on the first hyperbolic pair and use
its generation by these root groups. For the stated fields SL₂ is nontrivial
and perfect, contradicting solvability of the overgroup.

This is the matrix ingredient for the larger-field Borel placement used in
Aschbacher–Smith, combined manuscript of 1 March 2004, proof of 15.3.49 after
(k), printed p.1144. The flag, matrix carrier and root conventions are those
of `Flag.lean` and `FirstCohomologySymplecticFour/Generation.lean`.
-/

public section

open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F]
local notation "a" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "b" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "c" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "d" => (Sum.inr (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "SL" => SpecialLinearGroup (Fin 2) F

private def firstPairMatrix (A : SL) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks !![A 0 0, 0; 0, 1] !![A 0 1, 0; 0, 0]
    !![A 1 0, 0; 0, 0] !![A 1 1, 0; 0, 1]

private theorem firstPairMatrix_mem (A : SL) :
    firstPairMatrix A ∈ Matrix.symplecticGroup (Fin 2) F := by
  have hA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [det_fin_two] using A.property
  rw [firstPairMatrix, SymplecticGroup.fromBlocks_mem_iff]
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, mul_comm, hA]

private def firstPair : SL →* Sp F where
  toFun A := ⟨firstPairMatrix A, firstPairMatrix_mem A⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [firstPairMatrix]
  map_mul' A B := by
    apply Subtype.ext
    change firstPairMatrix (A * B) = firstPairMatrix A * firstPairMatrix B
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [firstPairMatrix, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

private theorem firstPair_injective : Function.Injective (firstPair (F := F)) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have he (x y : Fin 2 ⊕ Fin 2) := congrArg (fun g : Sp F => g.val x y) h
  fin_cases i <;> fin_cases j
  · exact he a a
  · exact he a c
  · exact he c a
  · exact he c c

private theorem firstPair_upper (t : F) :
    firstPair (SpecialLinearGroup.transvection zero_ne_one t) = rootElement 0 t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstPair, firstPairMatrix, SpecialLinearGroup.transvection_coe,
      rootElement, rootMatrix, single, fromBlocks]

private theorem firstPair_lower (t : F) :
    firstPair (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero t) =
      rootElement 1 t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstPair, firstPairMatrix, SpecialLinearGroup.transvection_coe,
      rootElement, rootMatrix, single, fromBlocks]

private theorem no_opposite_long_roots [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) (H : Subgroup (Sp F)) [Group.IsSolvable H]
    (hu : ∀ t : F, rootElement 0 t ∈ H)
    (hl : ∀ t : F, rootElement 1 t ∈ H) : False := by
  have hall (A : SL) : firstPair A ∈ H := by
    apply Matrix.SL2.transvection_induction (fun A => firstPair A ∈ H) ?_ ?_ A
    · intro i j hij t
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · simpa only [firstPair_upper] using hu t
      · simpa only [firstPair_lower] using hl t
      · exact (hij rfl).elim
    · intro A B hA hB
      simpa only [map_mul] using H.mul_mem hA hB
  let f : SL →* H := firstPair.codRestrict H hall
  have hf : Function.Injective f := by
    intro A B h
    exact firstPair_injective (congrArg Subtype.val h)
  have hsol : Group.IsSolvable SL := Group.isSolvable_of_isSolvable_injective hf
  have hlarge : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hlarge
  obtain ⟨u, hu⟩ := exists_ne (1 : Fˣ)
  have hu1 : (u : F) ≠ 1 := by simpa using hu
  have husq : (u : F) ^ 2 ≠ 1 := by
    intro h
    apply hu1
    exact (frobenius_inj F 2) (by simpa [frobenius_def] using h)
  let : Group.IsPerfect SL := ⟨Matrix.SL2.commutator_eq_top u.ne_zero husq⟩
  let : Nontrivial SL := ⟨⟨SpecialLinearGroup.transvection zero_ne_one (1 : F), 1, by
    intro h
    have he := congrArg (fun A : SL => A.val 0 1) h
    simp [SpecialLinearGroup.transvection_coe] at he⟩⟩
  exact Group.IsPerfect.not_isSolvable _ hsol

private theorem reduce_first_column (H : Subgroup (Sp F))
    (hU : unipotent ≤ H) (g : Sp F) (hg : g ∈ H) (hc : g.val c a ≠ 0) :
    ∃ w ∈ H, w.val a a = 0 ∧ w.val b a = 0 ∧ w.val d a = 0 ∧ w.val c a ≠ 0 := by
  let x := g.val a a
  let y := g.val b a
  let z := g.val c a
  let v := g.val d a
  let w := rootElement 0 (-(x + v / z * y) / z) *
    (rootElement 4 (-y / z) * (rootElement 6 (v / z) * g))
  have hw : w ∈ H := H.mul_mem
    (hU (positive_root_mem_unipotent 0 _ (by simp)))
    (H.mul_mem (hU (positive_root_mem_unipotent 4 _ (by simp)))
      (H.mul_mem (hU (positive_root_mem_unipotent 6 _ (by simp))) hg))
  refine ⟨w, hw, ?_, ?_, ?_, ?_⟩ <;>
    simp [w, x, y, z, v, rootElement, rootMatrix, mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks, single, hc]

private theorem pivot_paired_row (g : Sp F)
    (ha : g.val a a = 0) (hb : g.val b a = 0) (hd : g.val d a = 0)
    (j : Fin 2 ⊕ Fin 2) :
    g.val c a * g.val a j = -(1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) c j := by
  have hp := preserves_form g (e 0) (Pi.single j 1)
  fin_cases j <;>
    simp [-mul_eq_zero, form_apply, smul_eq_mulVec, e, mulVec_single,
      Fin.sum_univ_two, Matrix.one_apply, ha, hb, hd] at hp ⊢ <;>
    first | exact hp | linear_combination -hp

private theorem long_root_conjugate (g : Sp F)
    (ha : g.val a a = 0) (hb : g.val b a = 0) (hd : g.val d a = 0) (t : F) :
    g * rootElement 0 t * g⁻¹ = rootElement 1 (-(g.val c a ^ 2 * t)) := by
  have hr := pivot_paired_row g ha hb hd
  have hrb : g.val c a * g.val a b = 0 := by simpa using hr b
  have hrc : g.val c a * g.val a c = -1 := by simpa using hr c
  have hrd : g.val c a * g.val a d = 0 := by simpa using hr d
  have he : g * rootElement 0 t = rootElement 1 (-(g.val c a ^ 2 * t)) * g := by
    apply Subtype.ext
    change g.val * rootMatrix 0 t = rootMatrix 1 (-(g.val c a ^ 2 * t)) * g.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [-mul_eq_zero, rootMatrix, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
        fromBlocks, single, ha, hb, hd]
    all_goals first
    | linear_combination (g.val c a * t) * hrb
    | linear_combination (g.val c a * t) * hrc
    | linear_combination (g.val c a * t) * hrd
  rw [he, mul_inv_cancel_right]

/-- A solvable overgroup of the full standard unipotent subgroup has an
orthogonal standard point orbit over every nonbinary finite field of
characteristic two. -/
theorem solvable_unipotent_point_orbit_orthogonal [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) (H : Subgroup (Sp F))
    (hsol : Group.IsSolvable H) (hUH : unipotent ≤ H) :
    ∀ g ∈ H, form F (e 0) (g • e 0) = 0 := by
  let _ := hsol
  intro g hg
  suffices hz : g.val c a = 0 by
    simpa [form_apply, smul_eq_mulVec, e, mulVec_single] using hz
  by_contra hz
  obtain ⟨w, hw, ha, hb, hd, hc⟩ := reduce_first_column H hUH g hg hz
  apply no_opposite_long_roots hF H
    (fun t => hUH (positive_root_mem_unipotent 0 t (by simp)))
  intro t
  have hm := H.mul_mem (H.mul_mem hw
    (hUH (positive_root_mem_unipotent 0 (-(t / w.val c a ^ 2)) (by simp))))
    (H.inv_mem hw)
  rw [long_root_conjugate w ha hb hd] at hm
  simpa [mul_div_cancel₀ _ (pow_ne_zero 2 hc)] using hm

end Theory.SpecificGroups.SymplecticFour
