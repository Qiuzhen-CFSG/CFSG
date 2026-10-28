module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.LinearThree
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.ThreeAutomorphisms

import Mathlib.Tactic.FinCases

/-!
# Automorphism rigidity of the marked binary linear-three plane

An automorphism of SL₃(2) fixing the marked plane rotation and its radical
transvection is trivial. The inner/graph dichotomy reduces this to two small
matrix calculations. A matrix commuting with the two marks is scalar, hence
identity over F₂; a matrix intertwining their graph images has zero first row,
contradicting determinant one. Only the four literal matrix formulas use
kernel-checked computation.

This discharges the automorphism stabilizer calculation in the literal starred
centralizer argument for Aschbacher--Smith 15.3.31 and C.1.34. The automorphism
dichotomy comes from GLS3, Theorem 2.5.12 and §2.7, through the imported
binary three-dimensional automorphism theorem.
-/

public section

open Matrix
open scoped MatrixGroups
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.LinearThree
private theorem transvection_matrix : (planeTransvection : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    !![1,0,1;0,1,0;0,0,1] := by decide
private theorem rotation_matrix : (planeRotation : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    !![0,1,0;1,1,0;0,0,1] := by decide
private theorem graph_transvection_matrix : (graphSL 3 planeTransvection : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    !![1,0,0;0,1,0;1,0,1] := by decide
private theorem graph_rotation_matrix : (graphSL 3 planeRotation : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    !![1,1,0;1,0,0;0,0,1] := by decide

private theorem eq_one_of_commute_marked (g : SL)
    (ht : g * planeTransvection = planeTransvection * g)
    (hr : g * planeRotation = planeRotation * g) : g = 1 := by
  let M : Matrix (Fin 3) (Fin 3) (ZMod 2) := g
  have ht' : M * !![1,0,1;0,1,0;0,0,1] = !![1,0,1;0,1,0;0,0,1] * M := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul, transvection_matrix] using
      congrArg (fun x : SL => (x : Matrix (Fin 3) (Fin 3) (ZMod 2))) ht
  have hr' : M * !![0,1,0;1,1,0;0,0,1] = !![0,1,0;1,1,0;0,0,1] * M := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul, rotation_matrix] using
      congrArg (fun x : SL => (x : Matrix (Fin 3) (Fin 3) (ZMod 2))) hr
  have hr12 : M 1 2 = M 0 2 + M 1 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrArg (fun A => A 1 2) hr'
  have hc : M 0 2 = 0 := (add_eq_right.mp hr12.symm)
  have hf : M 1 2 = 0 := by
    have h : M 0 2 = M 1 2 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrArg (fun A => A 0 2) hr'
    exact h.symm.trans hc
  have hd : M 1 0 = 0 := by
    have h : M 1 0 + M 1 2 = M 1 2 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrArg (fun A => A 1 2) ht'
    exact add_eq_right.mp h
  have hb : M 0 1 = 0 := by
    have h : M 0 1 = M 1 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrArg (fun A => A 0 0) hr'
    exact h.trans hd
  have he : M 1 1 = M 0 0 := by
    have h : M 0 0 + M 0 1 = M 1 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrArg (fun A => A 0 1) hr'
    simpa only [hb, add_zero] using h.symm
  have hg : M 2 0 = 0 := by
    have h : M 2 0 + M 2 1 = M 2 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrArg (fun A => A 2 1) hr'
    exact add_eq_right.mp h
  have hh : M 2 1 = 0 := by
    have h : M 2 1 = M 2 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrArg (fun A => A 2 0) hr'
    exact h.trans hg
  have hi : M 2 2 = M 0 0 := by
    have h : M 0 0 + M 0 2 = M 0 2 + M 2 2 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrArg (fun A => A 0 2) ht'
    simpa only [hc, add_zero, zero_add] using h.symm
  have ha : M 0 0 = 1 := by
    have hz : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    apply hz
    intro ha0
    have hdet : M.det = 1 := g.det_coe
    simp [Matrix.det_fin_three, ha0, hb, hc] at hdet
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change M i j = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd, he, hf, hg, hh, hi]

private theorem no_graph_intertwiner_marked (g : SL)
    (ht : g * planeTransvection = graphSL 3 planeTransvection * g)
    (hr : g * planeRotation = graphSL 3 planeRotation * g) : False := by
  let M : Matrix (Fin 3) (Fin 3) (ZMod 2) := g
  have ht' : M * !![1,0,1;0,1,0;0,0,1] = !![1,0,0;0,1,0;1,0,1] * M := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul, transvection_matrix, graph_transvection_matrix] using
      congrArg (fun x : SL => (x : Matrix (Fin 3) (Fin 3) (ZMod 2))) ht
  have hr' : M * !![0,1,0;1,1,0;0,0,1] = !![1,1,0;1,0,0;0,0,1] * M := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul, rotation_matrix, graph_rotation_matrix] using
      congrArg (fun x : SL => (x : Matrix (Fin 3) (Fin 3) (ZMod 2))) hr
  have ha : M 0 0 = 0 := by
    have h : M 0 0 + M 0 2 = M 0 2 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrArg (fun A => A 0 2) ht'
    exact add_eq_right.mp h
  have hb : M 0 1 = 0 := by
    have h : M 2 1 = M 0 1 + M 2 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrArg (fun A => A 2 1) ht'
    exact add_eq_right.mp h.symm
  have hf : M 1 2 = 0 := by
    have h : M 0 2 = M 0 2 + M 1 2 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrArg (fun A => A 0 2) hr'
    exact add_eq_left.mp h.symm
  have hc : M 0 2 = 0 := by
    have h : M 1 2 = M 0 2 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrArg (fun A => A 1 2) hr'
    exact h.symm.trans hf
  have hdet : M.det = 1 := g.det_coe
  simp [Matrix.det_fin_three, ha, hb, hc] at hdet

private theorem inner_graph (α : MulAut SL) : ∃ g : SL,
    α = MulAut.conj g ∨ α = graphSL 3 * MulAut.conj g := by
  obtain ⟨g, hg⟩ := BinaryLinear.InvariantNodeActions.ThreeAutomorphisms.inner_graph
    (MulAut.congr (slEquivLinear 3) α)
  obtain ⟨k, rfl⟩ := (slEquivLinear 3).surjective g
  refine ⟨k, ?_⟩
  rcases hg with hi | hg
  · left
    ext x : 1
    apply (slEquivLinear 3).injective
    have hh := congrArg (fun β : MulAut (LinearGroup 3) => β (slEquivLinear 3 x)) hi
    simpa using hh
  · right
    ext x : 1
    apply (slEquivLinear 3).injective
    have hh := congrArg (fun β : MulAut (LinearGroup 3) => β (slEquivLinear 3 x)) hg
    simpa [graphLinear] using hh

/-- Fixing the actual marked radical transvection and plane rotation fixes
all of the binary three-dimensional special linear group. -/
theorem automorphism_eq_one_of_fixed_marked_matrices (α : MulAut SL)
    (ht : α planeTransvection = planeTransvection)
    (hr : α planeRotation = planeRotation) : α = 1 := by
  obtain ⟨g, hi | hg⟩ := inner_graph α
  · have hgt : g * planeTransvection = planeTransvection * g := by
      have h := congrArg (fun x => x * g) ht
      simpa [hi, MulAut.conj_apply, mul_assoc] using h
    have hgr : g * planeRotation = planeRotation * g := by
      have h := congrArg (fun x => x * g) hr
      simpa [hi, MulAut.conj_apply, mul_assoc] using h
    rw [hi, eq_one_of_commute_marked g hgt hgr, map_one]
  · have hγ (x : SL) : graphSL 3 (graphSL 3 x) = x :=
      congrArg (fun a : MulAut SL => a x) (graphSL_sq 3)
    have hgt : g * planeTransvection = graphSL 3 planeTransvection * g := by
      have h := congrArg (fun x => graphSL 3 x * g) ht
      simpa only [hg, MulAut.mul_apply, MulAut.conj_apply, hγ,
        mul_assoc, inv_mul_cancel, mul_one] using h
    have hgr : g * planeRotation = graphSL 3 planeRotation * g := by
      have h := congrArg (fun x => graphSL 3 x * g) hr
      simpa only [hg, MulAut.mul_apply, MulAut.conj_apply, hγ,
        mul_assoc, inv_mul_cancel, mul_one] using h
    exact (no_graph_intertwiner_marked g hgt hgr).elim
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.LinearThree
