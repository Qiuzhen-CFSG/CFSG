module
public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.Basic
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# The full automorphism fixer of the binary five-dimensional graph residual

Two cubic permutation matrices, on coordinates (012) and (234), are fixed
by inverse transpose. Their odd orders place them in the actual fixed
two-residual. A matrix commuting with both has one diagonal entry and one
off-diagonal entry; invertibility over F₂ forces it to be the identity.

The inner/graph automorphism theorem now shows that an automorphism fixing
the residual pointwise is identity or inverse transpose. In particular its
full pointwise fixer has order at most two. This argument needs neither a
complete residual identification nor the false printed inner-j₂ row.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.4(8),
printed p.1171, and the centralizer inspection in 16.4.9(1), printed p.1189.
The automorphism coverage is the proved binary instance of GLS3 2.5.12.
-/

@[expose] public section
open Subgroup Equiv Matrix
open scoped MatrixGroups
open BinaryLinear.OuterCyclic
open CFSG.Quasithin.Chapter16.LiePreliminaries
namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.BinaryLinear.FiveModel

private abbrev X := SL(5, ZMod 2)
private def qa : Perm (Fin 5) := swap 0 1 * swap 1 2
private def qb : Perm (Fin 5) := swap 2 3 * swap 3 4
private def a : X := ⟨qa.permMatrix (ZMod 2), by
  rw [det_permutation]; decide +kernel⟩
private def b : X := ⟨qb.permMatrix (ZMod 2), by
  rw [det_permutation]; decide +kernel⟩

private theorem commutes_entries (g : X) (hga : g * a = a * g) (hgb : g * b = b * g) :
    ∀ i j : Fin 5, g.val i j = if i = j then g.val 0 0 else g.val 0 1 := by
  have ha (i j : Fin 5) : g.val (qa i) (qa j) = g.val i j := by
    have he := congrArg (fun x : X => x.val i (qa j)) hga
    change (g.val * qa.permMatrix (ZMod 2)) i (qa j) =
      (qa.permMatrix (ZMod 2) * g.val) i (qa j) at he
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv] at he
    simpa using he.symm
  have hb (i j : Fin 5) : g.val (qb i) (qb j) = g.val i j := by
    have he := congrArg (fun x : X => x.val i (qb j)) hgb
    change (g.val * qb.permMatrix (ZMod 2)) i (qb j) =
      (qb.permMatrix (ZMod 2) * g.val) i (qb j) at he
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv] at he
    simpa using he.symm
  have ha' := ha
  have hb' := hb
  simp only [Fin.forall_fin_succ] at ha' hb'
  norm_num [qa, qb, Perm.mul_apply, swap_apply_def] at ha' hb'
  clear ha hb hga hgb
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num only [Fin.reduceEq, ite_true, ite_false] <;>
    grind only

private theorem commutes_eq_one (g : X) (hga : g * a = a * g) (hgb : g * b = b * g) : g = 1 := by
  have hg : g.val = fun i j => if i = j then g.val 0 0 else g.val 0 1 :=
    Matrix.ext (commutes_entries g hga hgb)
  have hc := g.property
  rw [hg] at hc
  have cases2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases cases2 (g.val 0 0) with hd | hd <;> rcases cases2 (g.val 0 1) with ho | ho
  all_goals rw [hd, ho] at hg hc
  · exact False.elim ((by decide +kernel :
      Matrix.det (fun i j : Fin 5 => if i = j then (0 : ZMod 2) else 0) ≠ 1) hc)
  · exact False.elim ((by decide +kernel :
      Matrix.det (fun i j : Fin 5 => if i = j then (0 : ZMod 2) else 1) ≠ 1) hc)
  · apply Subtype.ext
    exact hg
  · exact False.elim ((by decide +kernel :
      Matrix.det (fun i j : Fin 5 => if i = j then (1 : ZMod 2) else 1) ≠ 1) hc)

private theorem a_fixed : graphSL 5 a = a := by
  change (Matrix.SpecialLinearGroup.transpose a)⁻¹ = a
  apply inv_eq_of_mul_eq_one_left
  decide +kernel
private theorem b_fixed : graphSL 5 b = b := by
  change (Matrix.SpecialLinearGroup.transpose b)⁻¹ = b
  apply inv_eq_of_mul_eq_one_left
  decide +kernel

private theorem cubic_fixed_mem {Y : Type*} [Group Y] (t : MulAut Y) (y : Y)
    (hy : t y = y) (h3 : y ^ 3 = 1) : y ∈ fixedTwoResidual Y t := by
  let z : t.fixedSubgroup := ⟨y, (MulAut.mem_fixedSubgroup _ _).mpr hy⟩
  refine ⟨z, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  have hp : z ^ 3 = 1 := Subtype.ext h3
  exact (by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hp)

private noncomputable abbrev e := slEquivLinear 5
noncomputable abbrev graphResidual := fixedTwoResidual (LinearGroup 5) (graphLinear 5)

private theorem ea_fixed : graphLinear 5 (e a) = e a := by
  exact (graphLinear_slEquivLinear 5 a).trans (congrArg e a_fixed)
private theorem eb_fixed : graphLinear 5 (e b) = e b := by
  exact (graphLinear_slEquivLinear 5 b).trans (congrArg e b_fixed)
private theorem ea_mem : e a ∈ graphResidual := cubic_fixed_mem _ _ ea_fixed (by
  rw [← map_pow, show a ^ 3 = 1 from by decide +kernel, map_one])
private theorem eb_mem : e b ∈ graphResidual := cubic_fixed_mem _ _ eb_fixed (by
  rw [← map_pow, show b ^ 3 = 1 from by decide +kernel, map_one])

private theorem linear_commutes_eq_one (g : LinearGroup 5)
    (ha : g * e a = e a * g) (hb : g * e b = e b * g) : g = 1 := by
  have h : e.symm g = 1 := commutes_eq_one _ (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using ha) (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hb)
  exact e.symm.injective (h.trans e.symm.map_one.symm)

theorem fixer_coverage (f : MulAut (LinearGroup 5))
    (hf : f ∈ fixingSubgroup (MulAut (LinearGroup 5)) (graphResidual : Set (LinearGroup 5))) :
    f = 1 ∨ f = graphLinear 5 := by
  have ha : f (e a) = e a := ((mem_fixingSubgroup_iff _).mp hf) _ ea_mem
  have hb : f (e b) = e b := ((mem_fixingSubgroup_iff _).mp hf) _ eb_mem
  obtain ⟨g, rfl | rfl⟩ := inner_graph (Or.inr rfl) f
  · have hg : g = 1 := linear_commutes_eq_one g
      (mul_inv_eq_iff_eq_mul.mp ha) (mul_inv_eq_iff_eq_mul.mp hb)
    exact Or.inl (by rw [hg, map_one])
  · have hga : MulAut.conj g (e a) = e a :=
      (graphLinear 5).injective (ha.trans ea_fixed.symm)
    have hgb : MulAut.conj g (e b) = e b :=
      (graphLinear 5).injective (hb.trans eb_fixed.symm)
    have hg : g = 1 := linear_commutes_eq_one g
      (mul_inv_eq_iff_eq_mul.mp hga) (mul_inv_eq_iff_eq_mul.mp hgb)
    exact Or.inr (by rw [hg, map_one, mul_one])

theorem fixer_card_le_two :
    Nat.card (fixingSubgroup (MulAut (LinearGroup 5)) (graphResidual : Set (LinearGroup 5))) ≤ 2 := by
  classical
  let F := fixingSubgroup (MulAut (LinearGroup 5)) (graphResidual : Set (LinearGroup 5))
  let f : F → Fin 2 := fun a => if a.val = 1 then 0 else 1
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    obtain hx | hx := fixer_coverage x.val x.property
    · have hy : y.val = 1 := by
        by_contra hn
        have : (0 : Fin 2) = 1 := by simpa only [f, hx, if_pos, if_neg hn] using hxy
        exact (by decide : (0 : Fin 2) ≠ 1) this
      exact hx.trans hy.symm
    · obtain hy | hy := fixer_coverage y.val y.property
      · have hx' : x.val = 1 := by
          by_contra hn
          have : (1 : Fin 2) = 0 := by simpa only [f, hy, if_pos, if_neg hn] using hxy
          exact (by decide : (1 : Fin 2) ≠ 0) this
        exact hx'.trans hy.symm
      · exact hx.trans hy.symm
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

theorem fixer_not_four_dvd :
    ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut (LinearGroup 5)) (graphResidual : Set (LinearGroup 5))) := by
  let : Finite (LinearGroup 5) := Finite.of_equiv X e.toEquiv
  exact Nat.not_dvd_of_pos_of_lt Nat.card_pos (lt_of_le_of_lt fixer_card_le_two (by decide))

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.BinaryLinear.FiveModel
