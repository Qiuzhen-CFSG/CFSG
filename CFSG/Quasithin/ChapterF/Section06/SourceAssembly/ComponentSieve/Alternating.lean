module

public import Theory.GroupTheory.SmallSylowObstructions
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import CFSG.Quasithin.ClassicalModels
/-!
# Alternating models with a small elementary Sylow subgroup

An alternating group in the Theorem C range with an elementary Sylow
subgroup of order at most eight must have degree five. Smaller degrees
are solvable; degrees six and seven contain the explicit permutation
(0 1 2 3)(4 5), of order four; degree eight has order divisible by sixteen.
The actual icosahedral equivalence then gives PSL₂(5), preserving the
input model rather than recognizing a group from its order.

Source: Aschbacher–Smith F.6.17–18, printed pp.309–310.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G]
private def fourCycleSix : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5, by
    change Equiv.Perm.sign _ = 1
    norm_num
    decide⟩
private theorem fourCycleSix_order : orderOf fourCycleSix = 4 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · decide
  · decide
private def fourCycleSeven : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5, by
    change Equiv.Perm.sign _ = 1
    norm_num
    decide⟩
private theorem fourCycleSeven_order : orderOf fourCycleSeven = 4 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · decide
  · decide

theorem alternating_degree_of_small_elementary_sylow
    (P : Sylow 2 G) [IsElementaryAbelian 2 P] (hP : Nat.card P ≤ 8)
    (hns : ¬ Group.IsSolvable G) {n : ℕ} (hn : n ≤ 8)
    (e : G ≃* alternatingGroup (Fin n)) : n = 5 := by
  have h5 : 5 ≤ n := by
    by_contra! hh
    have hs : Group.IsSolvable (alternatingGroup (Fin n)) := by
      by_cases h4 : n = 4
      · subst n; exact alternatingGroup_fin_four_isSolvable
      · let := alternatingGroup.isMulCommutative_of_card_le_three
          (α := Fin n) (by simpa using (show n ≤ 3 by omega))
        exact Group.isSolvable_of_comm (isMulCommutative_iff.mp inferInstance)
    let := hs
    exact hns (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  have hno (x : alternatingGroup (Fin n)) : orderOf x ≠ 4 := by
    have hh := elementary_sylow_no_order_four P (e.symm x)
    simpa only [MulEquiv.orderOf_eq] using hh
  interval_cases n
  · rfl
  · exact (hno fourCycleSix fourCycleSix_order).elim
  · exact (hno fourCycleSeven fourCycleSeven_order).elim
  · have hh := not_sixteen_dvd_of_sylow_le_eight P hP
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hh
    norm_num at hh


theorem alternating_model_of_small_elementary_sylow
    (P : Sylow 2 G) [IsElementaryAbelian 2 P] (hP : Nat.card P ≤ 8)
    (hns : ¬ Group.IsSolvable G) {n : ℕ} (hn : n ≤ 8)
    (e : G ≃* alternatingGroup (Fin n)) : ClassicalGroup.IsPSL G 2 5 := by
  have hn5 := alternating_degree_of_small_elementary_sylow P hP hns hn e
  subst n
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  exact ⟨ZMod 5, inferInstance, inferInstance, Nat.card_zmod _, ⟨e.trans a.symm⟩⟩
end CFSG.Quasithin.ChapterF.SourceAssembly
