module
public import Theory.Mathieu.M22.Properties.FourNormalizers.Hexads
public import Theory.GroupTheory.PGroup.ThreeInvolutionAutomorphism
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.PGroup.FiveAutomorphismSmallCore
public import Theory.Mathieu.M22.Properties.LocalA5Shape.CoreNontrivial

/-!
# Intrinsic two-core shape for the normalized local A5 section in M22

An A5 quotient makes the two-core order divide thirty-two. An element of
order five in the original subgroup has no nonidentity fixed point on this
core: a fixed involution would put that element in an involution centralizer,
whose checked order is 384. Orbit counting and the Frattini subgroup force a
nontrivial such core to be elementary of order sixteen. The original full
Sylow normalization excludes the trivial core through its faithful action
on A5. All restrictions and quotient maps use the actual subgroup.

Source: Aschbacher--Smith A.3.12(12), A.3.14(6), pp.47--49, used in 10.2.9,
pp.750--751. No local subgroup catalogue or assumed shape is used here.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M22LocalA5Shape

private theorem core_card_dvd_thirtyTwo (B : Subgroup M22)
    (hq : Nat.card (B ⧸ pCore 2 B) = 60) : Nat.card (pCore 2 B) ∣ 32 := by
  have hd := B.card_subgroup_dvd_card
  rw [m22_order, ← (pCore 2 B).card_mul_index,
    show (pCore 2 B).index = 60 from hq] at hd
  have hd' : Nat.card (pCore 2 B) ∣ 32 * 231 :=
    (Nat.mul_dvd_mul_iff_right (by decide : 0 < 60)).mp hd
  have hc : Nat.Coprime (Nat.card (pCore 2 B)) 231 := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 231).pow_left n
  exact hc.dvd_of_dvd_mul_right hd'

private theorem order_five_core_action_fixedPointFree (B : Subgroup M22)
    (b : B) (hb : orderOf b = 5) :
    MonoidHom.FixedPointFree (MulAut.conjNormal b : MulAut (pCore 2 B)) := by
  apply (pCore_isPGroup (p := 2) (G := B)).fixedPointFree_of_no_fixed_prime_order
  intro x hx hfix
  have hxG : orderOf (x.val.val : M22) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  let c : centralizer ({x.val.val} : Set M22) := ⟨b.val, by
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg (fun y : pCore 2 B => y.val.val) hfix
    change b.val * x.val.val * b.val⁻¹ = x.val.val at he
    exact mul_inv_eq_iff_eq_mul.mp he⟩
  have hc : orderOf c = 5 := by
    exact (Subgroup.orderOf_coe c).symm.trans ((Subgroup.orderOf_coe b).trans hb)
  have hd := orderOf_dvd_natCard c
  rw [hc, M22FourNormalizers.involution_centralizer_card _ hxG] at hd
  norm_num at hd

/-- The actual alternating-five quotient and full Sylow normalization force
an elementary two-core of order sixteen. -/
theorem core_shape_of_normalized
    (S : Sylow 2 M22) (B : Subgroup M22)
    (hSB : (S : Subgroup M22) ≤ normalizer (B : Set M22))
    (eB : B ⧸ pCore 2 B ≃* alternatingGroup (Fin 5)) :
    IsElementaryAbelian 2 (pCore 2 B) ∧ Nat.card (pCore 2 B) = 16 := by
  have hq : Nat.card (B ⧸ pCore 2 B) = 60 := by
    rw [Nat.card_congr eB.toEquiv, nat_card_alternatingGroup]
    norm_num
  have h5 : 5 ∣ Nat.card B :=
    (by rw [hq]; decide : 5 ∣ Nat.card (B ⧸ pCore 2 B)).trans
      (card_quotient_dvd_card (pCore 2 B))
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 5 h5
  let a : MulAut (pCore 2 B) := MulAut.conjNormal b
  have ha : a ^ 5 = 1 := by
    change (MulAut.conjNormal b : MulAut (pCore 2 B)) ^ 5 = 1
    have hp : b ^ 5 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
    rw [← map_pow, hp, map_one]
  have hf : MonoidHom.FixedPointFree a := order_five_core_action_fixedPointFree B b hb
  rcases elementary_sixteen_of_free_five_small_core pCore_isPGroup
      (core_card_dvd_thirtyTwo B hq) a ha hf with h1 | h16
  · exact (core_ne_bot_of_normalized S B hSB eB (card_eq_one.mp h1)).elim
  · exact h16

end Sporadic.Mathieu.M22LocalA5Shape
