module
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderFive
public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.PrimeOrderLift
public import Theory.ElementaryAbelian.Injective

/-!
# Quintic actions on small two-cores

An order-five automorphism of a nonabelian two-group of order thirty-two
with Frattini subgroup of order two excludes elementary subgroups of order
eight. The square form on the Frattini quotient would otherwise have a
singular plane, contradicting the existing quadratic orbit count.

In a group of characteristic two, Cauchy's theorem supplies such an actor
whenever five divides the group order. The kernel of the canonical Frattini
action is the two-core, so the actor retains order five on both the core
and its quotient. This keeps the actor in the given ambient group.

Source: the Burnside basis-kernel theorem and the quadratic-form argument
for an order-thirty-two core in DGS, Groups and Graphs (1985), (10.9), p.163.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.QuinticFrattini

/-- A quintic automorphism excludes elementary subgroups of order eight. -/
theorem elementary_card_lt_eight {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (hnon : ¬ IsMulCommutative Q)
    (hcard : Nat.card Q = 32) (hphi : Nat.card (frattini Q) = 2)
    (a : MulAut Q) (ha : orderOf a = 5) :
    ∀ E : Subgroup Q, IsElementaryAbelian 2 E → Nat.card E < 8 := by
  intro E hE
  by_contra! hlarge
  obtain ⟨D,hDE,hD⟩ := Sylow.exists_subgroup_le_card_pow_prime_of_le_card
    (n := 3) Nat.prime_two hQ (by simpa using hlarge)
  have hDel : IsElementaryAbelian 2 D := hE.of_injective
    (inclusion hDE) (inclusion_injective _)
  let A := zpowers a
  have hA : Nat.card A = 5 := (Nat.card_zpowers a).trans ha
  exact SmallNonabelianTwoGroup.not_five_dvd_odd_actor_card_of_frattini_two
    hQ hnon hcard hphi D hDel (by simpa using hD) A
    (by rw [hA]; decide) (by rw [hA])

/-- Characteristic two supplies a quintic actor on the literal core and its Frattini quotient. -/
theorem exists_core_actor {H : Type*} [Group H] [Finite H]
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfive : 5 ∣ Nat.card H) :
    ∃ x : H, orderOf x = 5 ∧
      orderOf (MulAut.conjNormal (H := pCore 2 H) x) = 5 ∧
      orderOf (quotientAut (frattini (pCore 2 H))
        (MulAut.conjNormal (H := pCore 2 H) x)) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 5 hfive
  let f : H →* MulAut (pCore 2 H ⧸ frattini (pCore 2 H)) :=
    (quotientAut (frattini (pCore 2 H))).comp MulAut.conjNormal
  have hk : IsPGroup 2 f.ker := by
    rw [show f.ker = pCore 2 H from pCore_frattini_action_kernel 2 hc]
    exact pCore_isPGroup
  have hf : orderOf (f x) = 5 :=
    (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hk x (by rw [hx]; decide)).trans hx
  refine ⟨x,hx,?_,hf⟩
  apply Nat.dvd_antisymm
  · exact (orderOf_map_dvd (MulAut.conjNormal : H →* MulAut (pCore 2 H)) x).trans
      (by rw [hx])
  · rw [←hf]
    exact orderOf_map_dvd (quotientAut (frattini (pCore 2 H))) _


end Theory.GroupTheory.QuinticFrattini
