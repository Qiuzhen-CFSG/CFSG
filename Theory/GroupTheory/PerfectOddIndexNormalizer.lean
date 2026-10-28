module
public import FeitThompson.FinalTheorem
public import Mathlib.GroupTheory.IsPerfect
/-!
# A perfect normalizer containing a Sylow subgroup

If a perfect group normalizes L and the part of a subgroup R lying in it
has odd index and lies in L, then the quotient by its intersection with L
is perfect of odd order. The odd-order theorem makes that quotient trivial.
This supplies the opposite-parabolic containment in Aschbacher–Smith 2.4.11.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
lemma perfect_le_of_normalizes_of_odd_relIndex
    (A L R : Subgroup G) [Group.IsPerfect A]
    (hN : A ≤ normalizer (L : Set G)) (hRL : R ≤ L)
    (ho : Odd (R.subgroupOf A).index) : A ≤ L := by
  let J := L.subgroupOf A
  let : J.Normal := ⟨by
    intro x hx a
    exact (mem_normalizer_iff.mp (hN a.property) x.val).mp hx⟩
  have hRJ : R.subgroupOf A ≤ J := fun x hx => hRL hx
  have hoJ : Odd J.index := ho.of_dvd_nat (index_dvd_of_le hRJ)
  let : Group.IsSolvable (A ⧸ J) := odd_order_theorem _ (by rwa [index_eq_card] at hoJ)
  have hJ : J = ⊤ := by
    by_contra hj
    let : Nontrivial (A ⧸ J) := QuotientGroup.nontrivial_iff.mpr hj
    exact Group.IsPerfect.not_isSolvable (A ⧸ J) inferInstance
  exact subgroupOf_eq_top.mp hJ
end Theory.GroupTheory
