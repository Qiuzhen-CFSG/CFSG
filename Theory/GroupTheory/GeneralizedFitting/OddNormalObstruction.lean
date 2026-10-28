module

public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# Normal odd subgroups obstruct characteristic two

A normal q-subgroup lies in O_q and hence in the generalized Fitting subgroup.
If that subgroup equals O_p for a different prime p, disjointness of the two
prime cores forces the subgroup to be trivial. In particular a normal subgroup
of order three is incompatible with F* = O₂.

Source: standard finite-group theory; the order-three specialization is the
partition-stabilizer obstruction in Aschbacher--Smith 15.3.42, printed p.1138.
-/

public section

open Subgroup

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A normal q-subgroup vanishes when F* is the p-core and p differs from q. -/
theorem normal_pGroup_eq_bot_of_generalizedFitting_eq_pCore
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hne : p ≠ q)
    (hfit : generalizedFitting G = pCore p G)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup q N) : N = ⊥ := by
  have hq : N ≤ pCore q G := le_sSup ⟨inferInstance, hN⟩
  have hp : N ≤ pCore p G := hfit ▸
    hq.trans ((pCore_le_fitting G q).trans (fitting_le_generalizedFitting G))
  have hi := le_inf hp hq
  rw [(pCore_disjoint_of_ne p q hne).eq_bot] at hi
  exact le_bot_iff.mp hi

/-- An actual normal subgroup of order three obstructs characteristic two. -/
theorem not_characteristicTwo_of_normal_three
    (N : Subgroup G) [N.Normal] (hcard : Nat.card N = 3) :
    generalizedFitting G ≠ pCore 2 G := by
  intro h
  have hN : IsPGroup 3 N := IsPGroup.iff_card.mpr ⟨1, by simpa using hcard⟩
  have he := normal_pGroup_eq_bot_of_generalizedFitting_eq_pCore (by decide : 2 ≠ 3) h N hN
  have := N.card_eq_one.mpr he
  omega
end Theory.GroupTheory
