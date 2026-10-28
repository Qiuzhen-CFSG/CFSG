module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.EAction.PairCubic

/-!
# The complete coefficient table of the symmetric-pair model

The same-axis term is the triangle sum on three unscaled off-diagonal
matrices. The mixed term is supported on three distinct axes and one
unordered pair; the two orientations account for its coefficient minus eight.
The expansion of the triangle sum also supplies every degenerate zero case.
These are calculations of the existing pair model, independent of the Griess
comparison proved in the adjoining source modules.

Source: Aschbacher, *Sporadic Groups*, 29.11, printed pp. 159–160.
-/

@[expose] public section
open scoped BigOperators Matrix
open Sporadic.Monster Sporadic.Monster.Construction
open LocalC Griess NMonomial TrialitySpin Atlas.Codes
open TrialitySpin.SignedModules.Natural
namespace Sporadic.Monster.Construction.NMonomial.EAction.SourceCubic
noncomputable section
attribute [local instance] Classical.propDecidable

def edge (x y : Omega) : Matrix Omega Omega ℝ :=
  Matrix.single x y 1 + Matrix.single y x 1

def triangle (x y u v p q : Omega) : ℝ :=
  ∑ a, ∑ b, ∑ c, edge x y a b * edge u v b c * edge p q c a

theorem edge_apply (x y a b : Omega) : edge x y a b =
    (if a = x ∧ b = y then 1 else 0) + (if a = y ∧ b = x then 1 else 0) := by
  simp only [edge, Matrix.add_apply, Matrix.single, Matrix.of_apply, eq_comm]

theorem edge_indicator (x y : Omega) (hxy : x ≠ y) (a b : Omega) : edge x y a b =
    if (a = x ∧ b = y) ∨ (a = y ∧ b = x) then 1 else 0 := by
  rw [edge_apply]
  by_cases ha : a = x ∧ b = y <;> by_cases hb : a = y ∧ b = x <;> simp [ha, hb] <;> grind

theorem pairVector_entry (i a : Axis) (x y : Omega) (hxy : x ≠ y) (b c : Omega) :
    (pairVector i x y hxy).val a b c = if a = i then edge x y b c else 0 := by
  rw [edge_indicator x y hxy]
  simp only [pairVector, ite_and]

theorem sum_edge (x y : Omega) (f : Omega → Omega → ℝ) :
    (∑ a, ∑ b, edge x y a b * f a b) = f x y + f y x := by
  simp [edge_apply, add_mul, ite_and, ite_mul, Finset.sum_add_distrib]

theorem triangle_expansion (x y u v p q : Omega) : triangle x y u v p q =
    (if y = u then edge p q v x else 0) + (if y = v then edge p q u x else 0) +
    (if x = u then edge p q v y else 0) + (if x = v then edge p q u y else 0) := by
  unfold triangle
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [sum_edge]
  simp [edge_apply, add_mul, ite_and, ite_mul, Finset.sum_add_distrib]
  ring

theorem triangle_sum (i j k : Axis) (x y u v p q : Omega)
    (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q) :
    (∑ a : Axis, ∑ b : Omega, ∑ c : Omega, ∑ d : Omega,
      (pairVector i x y hxy).val a b c * (pairVector j u v huv).val a c d *
      (pairVector k p q hpq).val a d b) =
    if i = j ∧ j = k then triangle x y u v p q else 0 := by
  simp only [pairVector_entry, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hij : i = j <;> by_cases hjk : j = k <;> simp_all [triangle, eq_comm]

theorem pair_eq_iff (x y u v : Omega) :
    ({x,y} : Finset Omega) = {u,v} ↔ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  rw [← Finset.coe_inj]
  simpa using (Set.pair_eq_pair_iff (x := x) (y := y) (z := u) (w := v))

theorem edge_pair (x y u v : Omega) (huv : u ≠ v) :
    edge u v x y = if ({x,y} : Finset Omega) = {u,v} then 1 else 0 := by
  simp only [edge_indicator u v huv, pair_eq_iff]

theorem mixed_edges (x y u v p q : Omega) (huv : u ≠ v) (hpq : p ≠ q) :
    (∑ a, ∑ b, edge x y a b * edge u v a b * edge p q a b) =
      if ({x,y} : Finset Omega) = {u,v} ∧ ({u,v} : Finset Omega) = {p,q} then 2 else 0 := by
  simp_rw [mul_assoc]
  rw [sum_edge, edge_pair x y u v huv, edge_pair x y p q hpq,
    edge_pair y x u v huv, edge_pair y x p q hpq, Finset.pair_comm y x]
  split_ifs <;> simp_all
  norm_num

theorem sum_perms (f : Axis → Axis → Axis → ℝ) :
    (∑ σ : Equiv.Perm Axis, f (σ 0) (σ 1) (σ 2)) =
    f 0 1 2 + f 1 0 2 + f 2 1 0 + f 0 2 1 + f 1 2 0 + f 2 0 1 := by
  have hu : (Finset.univ : Finset (Equiv.Perm Axis)) =
      {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
        Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1} := by decide
  rw [hu]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  change f 0 1 2 + (f 1 0 2 + (f 2 1 0 + (f 0 2 1 + (f 1 2 0 + f 2 0 1)))) = _
  ring

theorem mixed_sum (i j k : Axis) (x y u v p q : Omega)
    (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q) :
    (∑ σ : Equiv.Perm Axis, ∑ a : Omega, ∑ b : Omega,
      (pairVector i x y hxy).val (σ 0) a b * (pairVector j u v huv).val (σ 1) a b *
      (pairVector k p q hpq).val (σ 2) a b) =
    if i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      ({x,y} : Finset Omega) = {u,v} ∧ ({u,v} : Finset Omega) = {p,q} then 2 else 0 := by
  rw [sum_perms (fun a b c => ∑ s : Omega, ∑ t : Omega,
    (pairVector i x y hxy).val a s t * (pairVector j u v huv).val b s t *
      (pairVector k p q hpq).val c s t)]
  simp only [pairVector_entry]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [mixed_edges x y u v p q huv hpq]

theorem pairBeta_table (i j k : Axis) (x y u v p q : Omega)
    (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q) :
    pairBeta (pairVector i x y hxy) (pairVector j u v huv) (pairVector k p q hpq) =
    (if i = j ∧ j = k then 4 * triangle x y u v p q else 0) +
    (if i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      ({x,y} : Finset Omega) = {u,v} ∧ ({u,v} : Finset Omega) = {p,q} then -8 else 0) := by
  rw [pairBeta_apply, triangle_sum, mixed_sum]
  split_ifs <;> ring

theorem edge_diagonal (x y : Omega) (hxy : x ≠ y) (a : Omega) : edge x y a a = 0 := by
  rw [edge_indicator x y hxy]
  apply if_neg
  rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
  · exact hxy h
  · exact hxy h.symm

theorem triangle_cycle (x y z : Omega) (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
    triangle x y y z z x = 1 := by
  rw [triangle_expansion]
  simp [edge_apply, hxy, hyz, hzx, hzx.symm]

theorem triangle_repeat (x y p q : Omega) (hxy : x ≠ y) (hpq : p ≠ q) :
    triangle x y x y p q = 0 := by
  rw [triangle_expansion]
  simp [hxy, hxy.symm, edge_diagonal p q hpq]

theorem triangle_disjoint (x y u v p q : Omega)
    (hxu : x ≠ u) (hxv : x ≠ v) (hyu : y ≠ u) (hyv : y ≠ v) :
    triangle x y u v p q = 0 := by
  rw [triangle_expansion]
  simp [hxu, hxv, hyu, hyv]

end
end Sporadic.Monster.Construction.NMonomial.EAction.SourceCubic
