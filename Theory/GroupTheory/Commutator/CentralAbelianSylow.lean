module

public import Theory.GroupTheory.Commutator.CentralSylowTransfer
public import Mathlib.GroupTheory.IsPerfect

/-!
# Central kernels and abelian Sylow subgroups

In a finite perfect group with an abelian Sylow p-subgroup, a central kernel
has order prime to p. A hypothetical central element of order p lies in every
Sylow p-subgroup. Central Sylow transfer puts it in the derived subgroup of
the abelian Sylow subgroup, a contradiction.

This is the transfer step for the defining-characteristic multiplier bound
for even PSL₂ (Aschbacher–Smith I.1.3–I.1.4; GLS III, Section 6.1).
-/

namespace CentralExtension

/-- An abelian Sylow subgroup excludes its prime from every central kernel
of a finite perfect group. -/
public theorem not_dvd_card_kernel_of_commutative_sylow {E B : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    [Group B] {p : ℕ} [Fact p.Prime] (f : E →* B)
    (hk : f.ker ≤ Subgroup.center E) (S : Sylow p E)
    (hS : ∀ v ∈ (S : Subgroup E), ∀ w ∈ (S : Subgroup E), Commute v w) :
    ¬ p ∣ Nat.card f.ker := by
  intro hd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hd
  have horder : orderOf (z : E) = p := (Subgroup.orderOf_coe z).trans hz
  let Z : Subgroup E := Subgroup.zpowers (z : E)
  have hZcenter : Z ≤ Subgroup.center E := Subgroup.zpowers_le.mpr (hk z.property)
  have hZnormal : Z.Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_center_iff.mp (hZcenter hx) g, mul_inv_cancel_right]
    exact hx
  let := hZnormal
  have hZp : IsPGroup p Z := IsPGroup.of_card (n := 1) (by
    dsimp [Z]; rw [Nat.card_zpowers, horder, pow_one])
  have hzS : (z : E) ∈ (S : Subgroup E) :=
    hZp.le_sylow_of_normal S (Subgroup.mem_zpowers _)
  have hcomm : ⁅(S : Subgroup E), (S : Subgroup E)⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact Subgroup.mem_bot.mpr (hS x hx y hy).commutator_eq
  have hzbot := hcomm (Subgroup.center_inf_commutator_inf_sylow_le_commutator S
    ⟨⟨hk z.property, Group.IsPerfect.mem_commutator⟩, hzS⟩)
  have hzone : (z : E) = 1 := Subgroup.mem_bot.mp hzbot
  rw [hzone, orderOf_one] at horder
  exact (Fact.out : p.Prime).ne_one horder.symm

end CentralExtension
