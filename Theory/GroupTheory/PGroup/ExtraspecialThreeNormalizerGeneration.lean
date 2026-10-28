module
public import Theory.GroupTheory.PGroup.ExtraspecialThreeInvolutionEndpoints
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupAction.QuotientConjugation
public import Theory.GroupTheory.Involution.Basic
import Mathlib.Tactic

/-!
# Involution generation above a center-fixing extraspecial 27-group

Every nontrivial center-fixing involutive automorphism of an extraspecial group
of order 27 inverts its Frattini quotient. Thus any two ambient involutions
have the same action there. Their product acts by an inner automorphism, so
a self-centralizing normal extraspecial subgroup contains that product.
If involutions generate the ambient group, any selected involution therefore
supplements the marked extraspecial subgroup.

This is the group-theoretic normalizer endpoint of Aschbacher–Smith D.2.29,
printed p.192. It needs no identification of the full outer automorphism group
and no separate exponent-three hypothesis.
-/

public section
noncomputable section
open Subgroup
local notation "IsInvolution" => BenderSuzuki.PFAppendixIII.IsInvolution
namespace IsExtraspecial
variable {G : Type*} [Group G] [Finite G]

private theorem mem_of_trivial_frattini_action
    (F : Subgroup G) [F.Normal] [IsExtraspecial 3 F]
    (hC : centralizer (F : Set G) ≤ F) (x : G)
    (hx : quotientAut (frattini F) (MulAut.conjNormal x) = 1) : x ∈ F := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hi : (MulAut.conjNormal x : MulAut F) ∈ (MulAut.conj : F →* MulAut F).range := by
    rw [← quotientAut_frattini_ker_eq_range_conj (p := 3)]
    exact hx
  obtain ⟨y, hy⟩ := hi
  have he : (MulAut.conjNormal (y : G) : MulAut F) = MulAut.conjNormal x := by
    rw [MulAut.conjNormal_val]
    exact hy
  have hc : (y : G)⁻¹ * x ∈ centralizer (F : Set G) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer F]
    change (MulAut.conjNormal ((y : G)⁻¹ * x) : MulAut F) = 1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hm := F.mul_mem y.property (hC hc)
  simpa only [mul_inv_cancel_left] using hm

omit [Finite G] in
private theorem involution_conjugation_ne_one
    (F : Subgroup G) [F.Normal] (hF : Nat.card F = 27)
    (hC : centralizer (F : Set G) ≤ F) (t : G) (ht : IsInvolution t) :
    (MulAut.conjNormal t : MulAut F) ≠ 1 := by
  intro he
  have hc : t ∈ centralizer (F : Set G) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer F]
    exact he
  have ho : orderOf t = 2 := orderOf_eq_prime ht.2 ht.1
  have hd := F.orderOf_dvd_natCard (hC hc)
  rw [ho,hF] at hd
  norm_num at hd

private theorem involution_frattini_inversion
    (F : Subgroup G) [F.Normal] [IsExtraspecial 3 F] (hF : Nat.card F = 27)
    (hC : centralizer (F : Set G) ≤ F)
    (t : G) (ht : IsInvolution t)
    (hZ : ∀ z ∈ center F, (MulAut.conjNormal t : MulAut F) z = z) :
    ∀ q : F ⧸ frattini F, quotientAut (frattini F) (MulAut.conjNormal t) q = q⁻¹ := by
  have hi : Function.Involutive (MulAut.conjNormal t : MulAut F) := by
    intro x
    have he := congrArg (fun a : MulAut F => a x)
      (show (MulAut.conjNormal t : MulAut F) * MulAut.conjNormal t = 1 by
        rw [← map_mul, ← pow_two, ht.2,map_one])
    exact he
  have hinv := (exponent_and_frattini_inversion_of_card27 hF (MulAut.conjNormal t) hi
    (involution_conjugation_ne_one F hF hC t ht) hZ).2
  intro q
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini F) q
  rw [quotientAut_apply_mk]
  exact hinv x

/-- Two center-fixing involutions differ by an element of the marked
self-centralizing extraspecial subgroup of order 27. -/
theorem involution_mul_mem_of_card27
    (F : Subgroup G) [F.Normal] [IsExtraspecial 3 F] (hF : Nat.card F = 27)
    (hC : centralizer (F : Set G) ≤ F)
    (s t : G) (hs : IsInvolution s) (ht : IsInvolution t)
    (hsZ : ∀ z ∈ center F, (MulAut.conjNormal s : MulAut F) z = z)
    (htZ : ∀ z ∈ center F, (MulAut.conjNormal t : MulAut F) z = z) : s*t ∈ F := by
  apply mem_of_trivial_frattini_action F hC
  rw [map_mul,map_mul]
  apply MulEquiv.ext
  intro q
  change quotientAut (frattini F) (MulAut.conjNormal s)
    (quotientAut (frattini F) (MulAut.conjNormal t) q) = q
  rw [involution_frattini_inversion F hF hC t ht htZ,
    involution_frattini_inversion F hF hC s hs hsZ,inv_inv]

/-- Involution generation gives the literal cyclic supplement; full
normalizer recognition and an exponent assumption are unnecessary. -/
theorem sup_involution_eq_top_of_card27
    (F : Subgroup G) [F.Normal] [IsExtraspecial 3 F] (hF : Nat.card F = 27)
    (hC : centralizer (F : Set G) ≤ F)
    (hgen : closure {s : G | IsInvolution s} = ⊤)
    (hZ : ∀ s : G, IsInvolution s → ∀ z ∈ center F,
      (MulAut.conjNormal s : MulAut F) z = z)
    (t : G) (ht : IsInvolution t) : F ⊔ zpowers t = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply (closure_le _).mpr
  intro s hs
  have hm : s*t ∈ F ⊔ zpowers t :=
    mem_sup_left (involution_mul_mem_of_card27 F hF hC s t hs ht (hZ s hs) (hZ t ht))
  have he : s*t*t⁻¹=s := by group
  exact he ▸ (F ⊔ zpowers t).mul_mem hm
    ((F ⊔ zpowers t).inv_mem (mem_sup_right (mem_zpowers t)))

end IsExtraspecial
