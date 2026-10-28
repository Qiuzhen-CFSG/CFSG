/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The translation and singular-root commutator proofs are adapted from
Atlas/LinearGroups/Orthogonal/PerfectAllCharD.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Changes: the exact CFSG binary carrier, coordinate decomposition of the base
root parameter space, and perfectness conditional only on singular transitivity.
-/
module
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.Simplicity.Basic
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Commutators in the binary split-eight elementary group

A spare hyperbolic coordinate pair expresses each coordinate root at `e₀`
as a commutator of two actual Siegel elements. Additivity of the parameter
then puts the entire root subgroup in the commutator subgroup. The parameter
along `e₀` gives the identity, and the parameter along `f₀` vanishes by
perpendicularity. Normal generation from the natural singular-vector action
therefore implies perfectness. This avoids the general complement-isometry
and field-size arguments of the all-characteristic ATLAS proof.

The consumer is the Iwasawa simplicity argument in the parent `Simplicity`
module. Its remaining geometric input is explicitly retained there.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.BinaryEightObstruction.Simplicity
open Quadratic
open scoped commutatorElement

theorem root_mem_commutator_of_translation (u a w : V) (hu : Q u = 0)
    (ha : Q.polarBilin u a = 0) (hw : Q.polarBilin u w = 0)
    (t : E) (htu : linear t u = u) (hta : linear t a = a + w) :
    root u w hu hw ∈ commutator E := by
  have haw : Q.polarBilin u (a + w) = 0 := by rw [map_add, ha, hw, add_zero]
  have hc : t * root u a hu ha * t⁻¹ = root u (a + w) hu haw := by
    simpa only [htu, hta] using root_conj t u a hu ha
  have he : ⁅t, root u a hu ha⁆ = root u w hu hw := by
    rw [commutatorElement_def, hc]
    have hadd : root u (a + w) hu haw = root u w hu hw * root u a hu ha := by
      simpa only [add_comm w a] using root_add u w a hu hw ha
    rw [hadd]
    group
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top t) (Subgroup.mem_top _)

/-- A spare hyperbolic pair realizes an orthogonal singular root as a commutator. -/
theorem singular_root_mem_commutator (u w a b : V)
    (hu : Q u = 0) (hw : Q w = 0) (hb : Q b = 0)
    (huw : Q.polarBilin u w = 0) (hua : Q.polarBilin u a = 0)
    (hub : Q.polarBilin u b = 0) (hwa : Q.polarBilin w a = 0)
    (hwb : Q.polarBilin w b = 0) (hab : Q.polarBilin a b = 1) :
    root u w hu huw ∈ commutator E := by
  have hbw : Q.polarBilin b (-w) = 0 := by
    rw [map_neg, polar_swap Q b w, hwb, neg_zero]
  apply root_mem_commutator_of_translation u a w hu hua huw (root b (-w) hb hbw)
  · change siegel Q b (-w) u = u
    simp only [siegel, map_neg, huw, hub, QuadraticMap.map_neg, hw, neg_zero,
      zero_smul, mul_zero, sub_zero, add_zero]
  · have haw : Q.polarBilin a (-w) = 0 := by
      rw [map_neg, polar_swap Q a w, hwa, neg_zero]
    change siegel Q b (-w) a = a + w
    simp only [siegel, haw, hab, QuadraticMap.map_neg, hw, zero_smul, one_smul,
      zero_mul, sub_zero, add_zero, sub_neg_eq_add]

private theorem base_root_self (c : K) :
    root (e 0) (c • e 0) (formD_e 0) (by rw [map_smul, polarD_e]; simp [e]) = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change siegel Q (e 0) (c • e 0) x = x
  have h := siegel_parameter_mod_line Q (e 0) 0 x c (formD_e 0) (by simp)
  simpa only [zero_add, siegel_zero] using h

private theorem base_root_e (i : Fin 4) (hi : i ≠ 0) :
    root (e 0) (e i) (formD_e 0) (by rw [polarD_e]; simp [e]) ∈ commutator E := by
  obtain ⟨j, hj, hji⟩ : ∃ j : Fin 4, j ≠ 0 ∧ j ≠ i := by
    fin_cases i <;> first | contradiction | decide
  apply singular_root_mem_commutator (e 0) (e i) (e j) (f j)
    (formD_e 0) (formD_e i) (formD_f j)
  all_goals simp only [polarD_e, polarD_f]
  all_goals simp [e, hj, hji]

private theorem base_root_f (i : Fin 4) (hi : i ≠ 0) :
    root (e 0) (f i) (formD_e 0) (by rw [polarD_f]; simp [e, Ne.symm hi]) ∈ commutator E := by
  obtain ⟨j, hj, hji⟩ : ∃ j : Fin 4, j ≠ 0 ∧ j ≠ i := by
    fin_cases i <;> first | contradiction | decide
  apply singular_root_mem_commutator (e 0) (f i) (e j) (f j)
    (formD_e 0) (formD_f i) (formD_f j)
  all_goals simp only [polarD_e, polarD_f]
  all_goals simp [e, f, hj, hji]

/-- All parameters of the base root subgroup lie in the elementary commutator. -/
theorem base_rootGroup_le_commutator : rootGroup (pointE 0) ≤ commutator E := by
  rintro _ ⟨v, rfl⟩
  let w : V := v.toAdd.val
  have hw : w (.inr 0) = 0 := by
    have hp : Q.polarBilin (e 0) w = 0 := v.toAdd.prop
    rwa [polar_swap, polarD_e] at hp
  have hs (i : Index 4) : ∃ hp : Q.polarBilin (e 0) (Pi.single i (w i)) = 0,
      root (e 0) (Pi.single i (w i)) (formD_e 0) hp ∈ commutator E := by
    cases i with
    | inl i =>
      have hp : Q.polarBilin (e 0) (Pi.single (.inl i) (w (.inl i))) = 0 := by
        rw [polar_swap, polarD_e]
        simp
      refine ⟨hp, ?_⟩
      generalize w (.inl i) = c at *
      fin_cases c
      · change root (e 0) (Pi.single (.inl i) 0) _ _ ∈ _
        simp only [Pi.single_zero, root_zero]
        exact (commutator E).one_mem
      · change root (e 0) (e i) _ _ ∈ _
        by_cases hi : i = 0
        · subst i
          have h := base_root_self 1
          simp only [one_smul] at h
          rw [h]
          exact (commutator E).one_mem
        · exact base_root_e i hi
    | inr i =>
      by_cases hi : i = 0
      · subst i
        simp only [hw, Pi.single_zero]
        exact ⟨by simp, by rw [root_zero]; exact (commutator E).one_mem⟩
      · have hp : Q.polarBilin (e 0) (Pi.single (.inr i) (w (.inr i))) = 0 := by
          rw [polar_swap, polarD_e]
          simp [hi]
        refine ⟨hp, ?_⟩
        generalize w (.inr i) = c at *
        fin_cases c
        · change root (e 0) (Pi.single (.inr i) 0) _ _ ∈ _
          simp only [Pi.single_zero, root_zero]
          exact (commutator E).one_mem
        · exact base_root_f i hi
  have hadd (x y : V)
      (hx : ∃ hp : Q.polarBilin (e 0) x = 0, root (e 0) x (formD_e 0) hp ∈ commutator E)
      (hy : ∃ hp : Q.polarBilin (e 0) y = 0, root (e 0) y (formD_e 0) hp ∈ commutator E) :
      ∃ hp : Q.polarBilin (e 0) (x+y) = 0, root (e 0) (x+y) (formD_e 0) hp ∈ commutator E := by
    obtain ⟨hx, hxc⟩ := hx
    obtain ⟨hy, hyc⟩ := hy
    refine ⟨by rw [map_add, hx, hy, add_zero], ?_⟩
    rw [root_add _ _ _ _ hx hy]
    exact (commutator E).mul_mem hxc hyc
  have hz : ∃ hp : Q.polarBilin (e 0) 0 = 0,
      root (e 0) 0 (formD_e 0) hp ∈ commutator E :=
    ⟨by simp, by rw [root_zero]; exact (commutator E).one_mem⟩
  have hall := Finset.sum_induction (s := Finset.univ) (f := fun i => Pi.single i (w i))
    (fun x => ∃ hp : Q.polarBilin (e 0) x = 0, root (e 0) x (formD_e 0) hp ∈ commutator E)
    hadd hz (fun i _ => hs i)
  rw [Finset.univ_sum_single] at hall
  exact hall.choose_spec

/-- Transitivity is the sole geometric input needed for perfectness. -/
theorem perfect_of_pretransitive [MulAction.IsPretransitive E Point] : Group.IsPerfect E :=
  ⟨eq_top_of_rootGroup_le (pointE 0) (commutator E) base_rootGroup_le_commutator⟩

end ClassicalOrthogonal.BinaryEightObstruction.Simplicity
