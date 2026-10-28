module

public import Theory.GroupAction.CoprimeQuotientOrbitBound
public import Mathlib.Tactic

/-!
# Transitivity in the equality case of a coprime orbit bound

A coprime action on a finite solvable group descends to an invariant quotient.
If every nonidentity actor fixes only elements of the kernel, the descended
action is free away from the identity. When the quotient has one more element
than the actor group, its nonidentity elements form a single orbit.

This is the orbit argument above the normal closure in GLS, Volume 4,
Chapter 2, Lemmas 15.6–15.7 (`refs/KGroup/GLS4/Chapter2.tex`).
-/

open Subgroup
namespace Theory.GroupAction

/-- The equality case of the coprime quotient orbit bound has one nonidentity orbit. -/
public theorem transitive_nonidentity_quotient_of_fixed_le
    {P K : Type*} [Group P] [Group K] [Finite P] [Finite K]
    [MulDistribMulAction K P] (R : Subgroup P) [R.Normal]
    (hR : IsInvariant K P R) (hsolv : Group.IsSolvable P)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card P))
    (hfixed : ∀ k : K, k ≠ 1 → ∀ x : P, k • x = x → x ∈ R)
    (hcard : Nat.card (P ⧸ R) = Nat.card K + 1) :
    letI : MulDistribMulAction K (P ⧸ R) := quotientMulDistribMulAction R hR
    ∀ x : P ⧸ R, x ≠ 1 → ∀ y : P ⧸ R, y ≠ 1 → ∃ k : K, k • x = y := by
  classical
  let : MulDistribMulAction K (P ⧸ R) := quotientMulDistribMulAction R hR
  intro x hx y hy
  let f : K → {a : P ⧸ R // a ≠ 1} := fun k => ⟨k • x, by
    intro hk
    exact hx ((MulDistribMulAction.toMulEquiv (P ⧸ R) k).injective
      (hk.trans (smul_one k).symm))⟩
  have hi : Function.Injective f := by
    intro b c heq
    have he : (c⁻¹ * b) • x = x := by
      rw [mul_smul, show b • x = c • x from congrArg Subtype.val heq, inv_smul_smul]
    have hcb : c⁻¹ * b = 1 := by
      by_contra hne
      exact hx (fixed_quotient_eq_one_of_fixed_le R hR hsolv hcop hfixed _ hne _ he)
    exact (inv_mul_eq_one.mp hcb).symm
  have hc : Nat.card {a : P ⧸ R // a ≠ 1} = Nat.card K := by
    let : Fintype (P ⧸ R) := Fintype.ofFinite _
    simp only [Nat.card_eq_fintype_card] at hcard ⊢
    rw [Fintype.card_subtype_compl (fun a : P ⧸ R => a = 1)]
    simp only [Fintype.card_unique]
    omega
  obtain ⟨k, hk⟩ := (hi.bijective_of_nat_card_le hc.le).2 ⟨y, hy⟩
  exact ⟨k, congrArg Subtype.val hk⟩

end Theory.GroupAction
