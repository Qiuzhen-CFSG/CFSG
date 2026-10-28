module

public import Theory.GroupTheory.CComponent.RadicalFree

/-!
# Commuting components when no simple normal subgroup exists

A finite nonsolvable group has a C-component. When the solvable radical is
trivial this component is nonabelian simple. If the group has no nonabelian
simple normal subgroup, a conjugate of the component is distinct from it;
the two components commute by the simple-subnormal subgroup theorem.

This gives an explicit pair for the multiple-component branch of subgroup
classification, without assuming a classification of the component carriers.
Source: Aschbacher–Smith, Proposition A.3.3(5)–(7), pp.42–43, together with
the conjugation criterion for normality.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- Absence of a nonabelian simple normal subgroup forces two distinct
commuting components in a finite nonsolvable group with trivial radical. -/
theorem exists_commuting_components_of_no_simple_normal
    (hnsolv : ¬ Group.IsSolvable G) (hR : solvableRadical G = ⊥)
    (hno : ∀ N : Subgroup G, N.Normal → IsSimpleGroup N →
      ¬ IsMulCommutative N → False) :
    ∃ L K : Subgroup G, L.IsCComponent ∧ K.IsCComponent ∧ L ≠ K ∧ ⁅L, K⁆ = ⊥ := by
  classical
  obtain ⟨L, hL⟩ := exists_isCComponent_of_not_isSolvable hnsolv
  have hn : ¬ L.Normal := fun hn => hno L hn
    (hL.isSimpleGroup_of_solvableRadical_eq_bot hR)
    (hL.not_isMulCommutative_of_solvableRadical_eq_bot hR)
  have hg : ∃ g : G, L.map (MulAut.conj g).toMonoidHom ≠ L := by
    by_contra h
    apply hn
    exact normal_iff_map_conj_eq.mpr (fun g => by simpa using not_exists.mp h g)
  obtain ⟨g, hg⟩ := hg
  have hK := hL.map_equiv (MulAut.conj g)
  exact ⟨L, L.map (MulAut.conj g).toMonoidHom, hL, hK, Ne.symm hg,
    hL.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hK (Ne.symm hg)⟩

end Subgroup
