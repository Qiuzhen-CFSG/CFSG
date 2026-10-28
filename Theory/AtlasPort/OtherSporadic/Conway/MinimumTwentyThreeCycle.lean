/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/MinimumTwentyThreeCycle.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OddMinimumOrthogonality
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu23PointStabilizer
public import Mathlib.GroupTheory.Perm.Cycle.Type
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/MinimumTwentyThreeCycle.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem minimum_point_cycle_exists (a : Omega) :
    ∃ g : Mathieu24CodeModel, g.val a = a ∧ orderOf g.val = 23 ∧
      g.val.IsCycle ∧ g.val.support = Finset.univ.erase a := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := Mathieu23PointModel a) 23
    (by rw [mathieu23_order]; norm_num)
  have ho : orderOf g.val.val = 23 := by simpa using hg
  have hc : g.val.val.IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (by rw [ho]; decide) (by rw [ho]; decide)
  refine ⟨g.val,g.prop,ho,hc,?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    apply Finset.mem_erase.mpr
    refine ⟨?_,Finset.mem_univ _⟩
    intro he
    subst i
    exact (Equiv.Perm.mem_support.mp hi) g.prop
  · rw [← hc.orderOf,ho,Finset.card_erase_of_mem (Finset.mem_univ _)]
    decide

theorem cycle_fixed_vector_constant (a : Omega) (g : Mathieu24CodeModel)
    (hc : g.val.IsCycle) (hs : g.val.support = Finset.univ.erase a)
    (x : IntegerCoordinates) (hx : integerPermutation g.val x = x) :
    ∃ b : ℤ, ∀ i, i ≠ a → x i = b := by
  obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.erase a).card by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; decide)
  refine ⟨x j,?_⟩
  have hm : ∀ i, x (g.val i) = x i := by
    intro i
    have he := congrFun hx (g.val i)
    change x (g.val.symm (g.val i)) = x (g.val i) at he
    simpa using he.symm
  have hp : ∀ n : ℕ, ∀ i, x ((g.val ^ n) i) = x i := by
    intro n
    induction n with
    | zero => intro i; rfl
    | succ n ih =>
      intro i
      rw [pow_succ',Equiv.Perm.mul_apply,hm,ih]
  intro i hi
  have hi' : g.val i ≠ i := Equiv.Perm.mem_support.mp (by rw [hs]; simp [hi])
  have hj' : g.val j ≠ j := Equiv.Perm.mem_support.mp (by rwa [hs])
  obtain ⟨n,hn⟩ := hc.exists_pow_eq hj' hi'
  rw [← hn]
  exact hp n j

theorem minimum_point_cycle_no_orthogonal_fixed_vector (a : Omega) :
    ∃ g : Mathieu24CodeModel, g.val a = a ∧ orderOf g.val = 23 ∧
      ∀ x : IntegerCoordinates, integerDot x x = 32 →
        integerDot (oddProfileBase {a} ∅) x = 0 → integerPermutation g.val x ≠ x := by
  obtain ⟨g,ha,ho,hc,hs⟩ := minimum_point_cycle_exists a
  refine ⟨g,ha,ho,?_⟩
  intro x hn hp hx
  obtain ⟨b,hb⟩ := cycle_fixed_vector_constant a g hc hs x hx
  exact odd_base_no_constant_orthogonal_minimum a x b hb hp hn

end Atlas.Conway
