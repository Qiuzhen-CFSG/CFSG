module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Lifting centrality from a quotient by a central p-subgroup

Let `N` be a central p-subgroup of a finite group `G`. If `x` centralizes
a Sylow p-subgroup and its image in `G / N` is central, then `x` is central
in `G`. This is the final centrality-lifting step of ABG Chapter II, Section 3,
Proposition 1 (article p22), stated independently of its Q-group hypotheses.

The map sending `g` to the commutator `[g,x]` has values in `N`; since those
values are central, it is a homomorphism. Its image is a p-group, while its
kernel contains a Sylow p-subgroup, so the image order is both a power of p
and prime to p. The image is therefore trivial, proving centrality.
-/

open scoped commutatorElement
namespace Subgroup
/-- Centrality modulo a central p-subgroup lifts when a Sylow subgroup
already centralizes the element. -/
public theorem mem_center_of_quotient_mem_center_of_centralizes_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hN : N ≤ center G) (hNp : IsPGroup p N)
    (S : Sylow p G) {x : G} (hx : x ∈ centralizer (S : Set G))
    (hbar : QuotientGroup.mk' N x ∈ center (G ⧸ N)) : x ∈ center G := by
  let q := QuotientGroup.mk' N
  have hc (g : G) : ⁅g, x⁆ ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ⁅g, x⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr ((mem_center_iff.mp hbar) (q g))
  let f : G →* N :=
    { toFun := fun g => ⟨⁅g, x⁆, hc g⟩
      map_one' := by ext; simp [commutatorElement_def]
      map_mul' := by
        intro a b
        apply Subtype.ext
        change ⁅a * b, x⁆ = ⁅a, x⁆ * ⁅b, x⁆
        rw [commutatorElement_mul_left_eq_conj_mul]
        rw [(mem_center_iff.mp (hN (hc b))) a]
        simp only [mul_assoc, mul_inv_cancel_left]
        exact (mem_center_iff.mp (hN (hc b)) ⁅a, x⁆).symm }
  have hker : (S : Subgroup G) ≤ f.ker := by
    intro s hs
    apply Subtype.ext
    change ⁅s, x⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.mpr ((mem_centralizer_iff.mp hx) s hs)
  have hrange : IsPGroup p f.range := hNp.to_subgroup f.range
  obtain ⟨n, hn⟩ := hrange.exists_card_eq
  have hindex : f.ker.index = p ^ n := (index_ker f).trans hn
  have hnzero : n = 0 := by
    by_contra hnzero
    apply S.not_dvd_index
    apply dvd_trans _ (index_dvd_of_le hker)
    rw [hindex]
    exact dvd_pow_self p hnzero
  have hkertop : f.ker = ⊤ := (index_eq_one.mp (by simpa [hnzero] using hindex))
  rw [mem_center_iff]
  intro g
  apply commutatorElement_eq_one_iff_mul_comm.mp
  have hg : g ∈ f.ker := by rw [hkertop]; trivial
  exact congrArg Subtype.val hg
end Subgroup
