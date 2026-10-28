module
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Residual control of normal subgroups over S₃

A normal subgroup of a finite group with quotient S₃ over its two-core
is either a two-group or contains the two-residual. The order is three
times a power of two, so divisibility by three decides the alternative.
A two-group residual forces the whole finite group to be a two-group.

Source application: Aschbacher--Smith 14.3.31, printed p.1003, controlling
the kernel of the original orbit-module action on KT.
-/

public section
open Subgroup Theory.GroupTheory
namespace SymmetricThreeTwoCore
variable {D : Type*} [Group D] [Finite D]

/-- A normal subgroup either has two-power order or contains O². -/
theorem normal_twoGroup_or_residual_le
    (e : (D ⧸ pCore 2 D) ≃* Equiv.Perm (Fin 3))
    (N : Subgroup D) [N.Normal] : IsPGroup 2 N ∨ pResidual 2 D ≤ N := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := D)).exists_card_eq
  have hc : Nat.card D = 3 * 2 ^ (n+1) := by
    rw [card_eq e,hn,pow_succ]
    ring
  by_cases h3 : 3 ∣ Nat.card N
  · right
    apply sInf_le
    refine ⟨inferInstance,IsPGroup.of_card_dvd_pow (n := n+1) ?_⟩
    obtain ⟨m,hm⟩ := h3
    have hi := N.index_mul_card
    rw [hc,hm] at hi
    change N.index ∣ 2 ^ (n+1)
    exact ⟨m,by nlinarith [hi]⟩
  · left
    apply IsPGroup.of_card_dvd_pow (n := n+1)
    have hd := N.card_subgroup_dvd_card
    rw [hc] at hd
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm.dvd_mul_left.mp hd

end SymmetricThreeTwoCore

namespace Subgroup
variable {D : Type*} [Group D] [Finite D]
/-- A finite group with p-group p-residual is itself a p-group. -/
theorem isPGroup_of_residual_isPGroup (p : ℕ) (h : IsPGroup p (pResidual p D)) :
    IsPGroup p D := by
  intro x
  obtain ⟨n,hn⟩ := isPGroup_quotient_pResidual p (QuotientGroup.mk' (pResidual p D) x)
  have hx : x ^ p ^ n ∈ pResidual p D := (QuotientGroup.eq_one_iff _).mp (by
    change (QuotientGroup.mk' (pResidual p D)) (x ^ p ^ n) = 1
    rw [map_pow]
    exact hn)
  obtain ⟨m,hm⟩ := h ⟨x ^ p ^ n,hx⟩
  refine ⟨n+m,?_⟩
  have hh := congrArg Subtype.val hm
  simpa only [coe_pow,coe_one,←pow_mul,←pow_add] using hh
end Subgroup

