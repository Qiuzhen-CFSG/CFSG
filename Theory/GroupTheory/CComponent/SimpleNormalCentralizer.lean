module

public import Theory.GroupTheory.CComponent.RadicalFree

/-!
# Centralizers of simple normal subgroups in radical-free groups

Let `S` be a nonabelian simple normal subgroup of a finite group with trivial
solvable radical. If its centralizer is nontrivial, that normal centralizer
cannot be solvable. A C-component of the centralizer lifts to a C-component
of the whole group, distinct from and commuting with `S`.

In the complementary case every nontrivial normal subgroup contains `S`:
the simple-subnormal dichotomy makes a normal subgroup either contain `S`
or centralize it. This is the elementary reduction to the almost-simple
case; it makes no assertion about the isomorphism type of `S`.

Source: the solvable radical and the component calculus in
Aschbacher–Smith, Proposition A.3.3(2), (5)–(7), printed pp.42–43.
-/

public section

namespace Subgroup

private theorem perfect_of_nonabelian {H : Type*} [Group H] [IsSimpleGroup H]
    (ha : ¬ IsMulCommutative H) : Group.IsPerfect H := by
  refine ⟨?_⟩
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator H)
    inferInstance).resolve_left (fun h => ha ((commutator_eq_bot_iff H).mp h))

/-- A nontrivial centralizer of a simple normal subgroup in a finite
radical-free group supplies a second, commuting C-component. -/
theorem exists_commuting_component_of_simple_normal_centralizer_ne_bot
    {G : Type*} [Group G] [Finite G] (S : Subgroup G) [S.Normal] [IsSimpleGroup S]
    (hR : solvableRadical G = ⊥) (ha : ¬ IsMulCommutative S)
    (hC : centralizer (S : Set G) ≠ ⊥) :
    ∃ K : Subgroup G, S.IsCComponent ∧ K.IsCComponent ∧ S ≠ K ∧ ⁅S, K⁆ = ⊥ := by
  let := perfect_of_nonabelian ha
  have hS : S.IsCComponent := isCComponent_of_isSimpleGroup_of_isPerfect
    (inferInstance : S.Normal).isSubnormal
  let C := centralizer (S : Set G)
  have hnsolv : ¬ Group.IsSolvable C := by
    intro hsolv
    exact hC (le_bot_iff.mp ((le_solvableRadical C inferInstance hsolv).trans hR.le))
  obtain ⟨K, hK⟩ := exists_isCComponent_of_not_isSolvable hnsolv
  have hKC : K.map C.subtype ≤ C := by simpa using map_le_range C.subtype K
  have hKG : (K.map C.subtype).IsCComponent :=
    hK.map_subtype (inferInstance : C.Normal).isSubnormal
  have hne : S ≠ K.map C.subtype := by
    intro he
    exact ha (le_centralizer_iff_isMulCommutative.mp (he.le.trans hKC))
  refine ⟨K.map C.subtype, hS, hKG, hne, ?_⟩
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hKC

/-- A self-centralizing nonabelian simple normal subgroup is contained in
every nontrivial normal subgroup. No finiteness assumption is needed. -/
theorem simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot
    {G : Type*} [Group G] (S : Subgroup G) [S.Normal] [IsSimpleGroup S]
    (ha : ¬ IsMulCommutative S) (hC : centralizer (S : Set G) = ⊥)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : S ≤ N := by
  let := perfect_of_nonabelian ha
  rcases simple_subnormal_normal_dichotomy S N
      (inferInstance : S.Normal).isSubnormal with h | h
  · exact h
  · exfalso
    apply hN
    rw [commutator_comm] at h
    exact le_bot_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp h).trans hC.le)

end Subgroup
