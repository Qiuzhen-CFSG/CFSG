module
public import Theory.GroupTheory.Commutator.CentralFixedMoved
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# Centrality of an abelian coprime fixed subgroup

If a coprime actor T normalizes a finite solvable subgroup K and fixes K',
then C_K(T) centralizes [K,T] by the three-subgroups lemma. When C_K(T)
is abelian, the decomposition K = [K,T] C_K(T) makes it central in K.
Only relative normality in the ambient group is used.

This supplies the center obstruction for the subgroup X in Fong--Seitz I,
(6F), printed p.47, using its full cubic fixed subgroup.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
/-- An abelian coprime fixed subgroup is central when the actor fixes the derived subgroup. -/
theorem fixed_le_centralizer_of_derived_fixed_of_abelian {G : Type*} [Group G] [Finite G]
    (K T : Subgroup G) (hn : T ≤ normalizer (K : Set G))
    (hs : Group.IsSolvable K) (hc : Nat.Coprime (Nat.card T) (Nat.card K))
    (hd : ⁅K,K⁆ ≤ centralizer (T : Set G))
    (ha : IsMulCommutative ↥(K ⊓ centralizer (T : Set G))) :
    K ⊓ centralizer (T : Set G) ≤ centralizer (K : Set G) := by
  let C := K ⊓ centralizer (T : Set G)
  let := ha
  have hm : C ≤ centralizer (↑(⁅K,T⁆) : Set G) :=
    (commutator_centralizes_iff_centralizes_moved K T C inf_le_left hd).mp (by
      rw [commutator_eq_bot_iff_le_centralizer.mpr (show C ≤ centralizer (T : Set G) from inf_le_right)]
      exact bot_le)
  apply le_centralizer_iff.mp
  change K ≤ centralizer (C : Set G)
  conv_lhs => rw [eq_commutator_sup_centralizer_of_solvable_coprime K T hn hs hc]
  exact sup_le (le_centralizer_iff.mp hm) C.le_centralizer
end Subgroup
