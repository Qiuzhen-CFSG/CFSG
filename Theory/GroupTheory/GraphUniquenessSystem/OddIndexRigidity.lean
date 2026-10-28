module
public import Theory.GroupTheory.GraphUniquenessSystem.LocalComparison
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-!
# Odd-index detection of automorphisms

If an automorphism fixes an abelian self-centralizing normal subgroup N,
its displacement is a crossed homomorphism into N. When it fixes an
odd-index overgroup H, average that crossed homomorphism over the literal
cosets G/H. In exponent two the average makes it principal, with its
conjugating element fixed by H. Thus C_N(H)=1 forces the automorphism to be
trivial.

The application is the actual edge-fixer rigidity in Aschbacher, *Sporadic
Groups* (1994), 38.5 and 41.4, printed pp.206, 222. This elementary abelian
case avoids stronger automorphism and cohomology classification assumptions.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.GraphUniquenessSystem

private theorem crossed_eq_one_of_odd_index
    {G A : Type*} [Group G] [Finite G] [CommGroup A]
    (H : Subgroup G) (ρ : G →* MulAut A) (δ : G → A)
    (hmul : ∀ g k, δ (g * k) = δ g * ρ g (δ k))
    (hH : ∀ h ∈ H, δ h = 1) (hpow : ∀ a : A, a ^ 2 = 1)
    (hodd : Odd H.index)
    (hfixed : ∀ a : A, (∀ h : H, ρ h a = a) → a = 1) : ∀ g, δ g = 1 := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  let d : G ⧸ H → A := Quotient.lift δ (by
    intro a b hab
    have hh := hH (a⁻¹ * b) (QuotientGroup.leftRel_apply.mp hab)
    have he := hmul a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hh, map_one, mul_one] at he
    exact he.symm)
  have hd (g : G) (q : G ⧸ H) : d (g • q) = δ g * ρ g (d q) := by
    induction q using QuotientGroup.induction_on with
    | H a => exact hmul g a
  let c : A := ∏ q : G ⧸ H, d q
  have hc (g : G) : c = δ g * ρ g c := by
    have hr : c = ∏ q : G ⧸ H, d (g • q) :=
      (Fintype.prod_equiv (MulAction.toPerm g) (fun q => d (g • q)) d (fun _ => rfl)).symm
    conv_lhs => rw [hr]
    simp_rw [hd]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← map_prod]
    have hp : δ g ^ Fintype.card (G ⧸ H) = δ g := by
      rw [← Nat.card_eq_fintype_card, ← index_eq_card]
      obtain ⟨k, hk⟩ := hodd
      rw [hk, pow_add, pow_mul, hpow, one_pow, pow_one, one_mul]
    rw [hp]
  have hc1 : c = 1 := hfixed c (by
    intro h
    have hh := hc h
    rw [hH h h.property, one_mul] at hh
    exact hh.symm)
  intro g
  have hh := hc g
  rw [hc1, map_one, mul_one] at hh
  exact hh.symm

open scoped IsMulCommutative

/-- A fixed odd-index overgroup detects automorphisms of a group with an
abelian self-centralizing normal two-subgroup, provided that overgroup has
no fixed point in the normal subgroup. -/
theorem automorphismRigid_of_odd_index
    {G : Type*} [Group G] [Finite G]
    (N H : Subgroup G) [N.Normal] [IsMulCommutative N]
    (hNH : N ≤ H) (hself : centralizer (N : Set G) ≤ N)
    (hpow : ∀ n : N, n ^ 2 = 1) (hodd : Odd H.index)
    (hfixed : N ⊓ centralizer (H : Set G) = ⊥) : AutomorphismRigid H := by
  intro α hα
  have hfix (h : G) (hh : h ∈ H) : α h = h := hα ⟨h, hh⟩
  have hδ (g : G) : α g * g⁻¹ ∈ N := by
    apply hself
    apply mem_centralizer_iff.mpr
    intro n hn
    have hi : g⁻¹ * n * g ∈ N := by
      simpa only [inv_inv] using (inferInstance : N.Normal).conj_mem n hn g⁻¹
    have he := hfix (g⁻¹ * n * g) (hNH hi)
    rw [map_mul, map_mul, map_inv, hfix n (hNH hn)] at he
    have hh := congrArg (fun a => α g * a * g⁻¹) he
    group at hh
    simpa only [mul_assoc, zpow_neg_one] using hh
  let δ : G → N := fun g => ⟨α g * g⁻¹, hδ g⟩
  have he := crossed_eq_one_of_odd_index H (MulAut.conjNormal : G →* MulAut N) δ
    (by intro g k; apply Subtype.ext; simp [δ, map_mul, mul_assoc])
    (by intro h hh; apply Subtype.ext; simp [δ, hfix h hh]) hpow hodd (by
      intro a ha
      apply Subtype.ext
      have hc : (a : G) ∈ centralizer (H : Set G) := by
        apply mem_centralizer_iff.mpr
        intro h hh
        have he := congrArg Subtype.val (ha ⟨h, hh⟩)
        change h * (a : G) * h⁻¹ = a at he
        exact (mul_inv_eq_iff_eq_mul.mp he)
      have hm : (a : G) ∈ N ⊓ centralizer (H : Set G) := ⟨a.property, hc⟩
      rwa [hfixed, mem_bot] at hm)
  ext g
  have hh := congrArg Subtype.val (he g)
  exact mul_inv_eq_one.mp hh

end Theory.GroupTheory.GraphUniquenessSystem
