module

public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.IsPerfect

/-!
# The center of a perfect group lies in its Frattini subgroup

If a maximal subgroup omits a central element, it and the center generate
the whole group. The maximal subgroup is then normal, and the resulting
abelian quotient contradicts perfectness. Thus every maximal subgroup
contains the center. The proof does not require finiteness.

This is the central-supplement argument used for the component alternative
in Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma D.3.4(2),
printed p.194.
-/

public section
open scoped IsMulCommutative

namespace Subgroup
/-- Every central element of a perfect group belongs to every maximal subgroup. -/
theorem center_le_frattini_of_isPerfect {G : Type*} [Group G] [Group.IsPerfect G] :
    center G ≤ frattini G := by
  unfold frattini Order.radical
  refine le_iInf fun M => le_iInf fun hM => ?_
  by_contra hn
  have hsup : M ⊔ center G = ⊤ := codisjoint_iff.mp (hM.not_le_iff_codisjoint.mp hn)
  let : M.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← hsup]
    exact sup_le M.le_normalizer (center_le_normalizer (M : Set G))))
  have hc : _root_.commutator G ≤ M :=
    Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
  rw [Group.IsPerfect.commutator_eq_top] at hc
  exact hM.ne_top (top_unique hc)

/-- A central supplement cannot enlarge a subgroup of a perfect group
to the whole group. This is the nongeneration step in A.2.11. -/
theorem eq_top_of_sup_center_eq_top {G : Type*} [Group G] [Group.IsPerfect G]
    (U : Subgroup G) (hU : U ⊔ center G = ⊤) : U = ⊤ := by
  let : U.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← hU]
    exact sup_le U.le_normalizer (center_le_normalizer (U : Set G))))
  have hc : _root_.commutator G ≤ U :=
    Normal.commutator_le_of_self_sup_commutative_eq_top hU inferInstance
  rw [Group.IsPerfect.commutator_eq_top] at hc
  exact top_unique hc
end Subgroup
