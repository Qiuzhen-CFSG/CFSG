module
public import Theory.GroupAction.ComponentRankAction.ResidualSource
/-!
# Prime-to-odd-prime residuals with a two-group outer action

For a component of full odd prime rank two, the rank bound makes its
centralizer prime-to-p. A two-group outer automorphism quotient makes all
p-elements act internally, so coprime-kernel absorption recovers the
original component as the prime-to-p residual and prime-generated closure.
Source: Aschbacher–Smith A.3.18, printed pp.51–53.
-/
public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupAction.ComponentRankAction
variable {G S : Type*} [Group G] [Finite G] [Group S] {p : ℕ} [Fact p.Prime]
theorem component_eq_primeClosure_and_residual_of_outer_twoGroup
    {L : Subgroup G} (hL : IsComponent G L)
    (hz : Nat.Coprime p (Nat.card (center L)))
    (hr : 2 ≤ primeRank p L) (hG : primeRank p G ≤ 2)
    (e : L ⧸ center L ≃* S) (ho : Odd p)
    (houter : IsPGroup 2 (MulAut.Outer S)) :
    L = closure {x : G | orderOf x = p} ∧ L = primeToResidual p G := by
  apply component_eq_primeClosure_and_residual hL hz hr hG e
  intro a _ m hm
  let q := QuotientGroup.mk' (MulAut.innerSubgroup S)
  apply (QuotientGroup.eq_one_iff a).mp
  obtain ⟨k,hk⟩ := houter (q a)
  have hq : (q a)^(p^m)=1 := by rw [←map_pow,hm,map_one]
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_left.mpr ho).pow k m)
    (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one hq)
end Theory.GroupAction.ComponentRankAction
