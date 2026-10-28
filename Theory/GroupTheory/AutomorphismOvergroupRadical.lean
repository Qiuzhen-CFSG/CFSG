module
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.CComponent.RadicalFree

/-!
# The radical of an automorphism overgroup

A subgroup of Aut(Q) containing Inn(Q), for Q centerless, simple and perfect,
has trivial solvable radical. The radical cannot contain the simple inner
subgroup; the normal-subgroup dichotomy therefore makes it centralize that
subgroup, whose centralizer in Aut(Q) is trivial.

Source application: Aschbacher--Smith 10.2.9, printed p.752, the original
quotient action of a containing binary-linear Sylow overgroup.
-/

public noncomputable section
open Subgroup
namespace MulAut
/-- Every subgroup of Aut(Q) containing Inn(Q) is radical-free for centerless
simple perfect Q. -/
theorem radical_free_of_inner_le {Q : Type*} [Group Q] [Finite Q]
    [IsSimpleGroup Q] [Group.IsPerfect Q] (hz : center Q = ⊥)
    (A : Subgroup (MulAut Q)) (hi : innerSubgroup Q ≤ A) : solvableRadical A = ⊥ := by
  let B := (innerSubgroup Q).subgroupOf A
  let e : Q ≃* B := (MonoidHom.ofInjective (conj_injective_of_center_eq_bot hz)).trans
    (subgroupOfEquivOfLe hi).symm
  let : IsSimpleGroup B := e.symm.isSimpleGroup
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hB : B.IsSubnormal := (inferInstance : B.Normal).isSubnormal
  rcases simple_subnormal_normal_dichotomy B (solvableRadical A) hB with h | h
  · have hs : Group.IsSolvable B :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective h)
    exact (Group.IsPerfect.not_isSolvable B hs).elim
  · apply bot_unique
    intro a ha
    rw [commutator_comm] at h
    have hc := commutator_eq_bot_iff_le_centralizer.mp h ha
    have hh : a.val ∈ centralizer (innerSubgroup Q : Set (MulAut Q)) := by
      intro g hg
      exact congrArg A.subtype (hc ⟨g,hi hg⟩ hg)
    rw [centralizer_innerSubgroup_eq_bot hz,mem_bot] at hh
    exact Subtype.ext hh
end MulAut
