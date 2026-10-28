module
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Mathlib.GroupTheory.Nilpotent

/-!
# A stationary Thompson subgroup terminates the normalizer tower

If M is the elementary Thompson subgroup of N_P(M), every normalizer of
N_P(M) also normalizes M. Thus N_P(M) is self-normalizing in the finite
two-group P and equals P by the normalizer condition.

Source: Aschbacher–Smith C.6.4, printed p.169. This argument needs no
normalizer-index hypothesis and applies to every dihedral overgroup M.
-/

public section

open Subgroup Stellmacher
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem twoGroup_normalizer_eq_of_thompson_eq (P M : Subgroup G)
    (hp : IsPGroup 2 P)
    (hJ : elementaryAbelianMaxJ (P ⊓ normalizer (M : Set G)) = M) :
    P ⊓ normalizer (M : Set G) = P := by
  let N := P ⊓ normalizer (M : Set G)
  have hNP : N ≤ P := inf_le_left
  have hself : P ⊓ normalizer (N : Set G) ≤ N := by
    refine le_inf inf_le_left ?_
    have hh := normalizer_le_normalizer_elementaryAbelianMaxJ N
    rw [hJ] at hh
    exact inf_le_right.trans hh
  let : Group.IsNilpotent P := hp.isNilpotent
  have he : normalizer (N.subgroupOf P : Set P) = N.subgroupOf P := by
    apply le_antisymm ?_ le_normalizer
    rw [← subgroupOf_normalizer_eq hNP]
    intro g hg
    exact hself ⟨g.property,hg⟩
  have ht := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := P)) _ he
  exact le_antisymm hNP (subgroupOf_eq_top.mp ht)
end Theory.GroupTheory
