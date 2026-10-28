module

public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index

/-!
# Fixed spaces across sections and odd-index central extensions

For a binary K-module and B of odd index, sum the translates of a B-fixed
vector over K/B. This sum is K-fixed and differs from the original vector
by an element of W whenever K acts trivially on U/W. If the B-fixed vectors
in W are K-fixed, the original vector is therefore K-fixed as well.

Equivariant maps and actual quotient coordinates supply the fixed-space
containments for one or two noncentral layers above a central submodule.
No semisimplicity or splitting of the extension is assumed.

Source: the natural-layer extension arguments in Aschbacher–Smith,
combined manuscript (1 March 2004), proof of 13.8.20,
printed pp.954–955 (PDF pp.971–972).
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace Representation.HigherFieldBorelFixedSpaces
variable {K U : Type*} [Group K] [AddCommGroup U] [Module (ZMod 2) U]

/-- Equality of fixed spaces lifts through a central quotient at odd index.
The displacement condition is precisely triviality of the action on U/W;
it also implies that W is invariant. Only K/B needs to be finite. -/
theorem odd_index_fixedSpace_extension
    (ρ : Representation (ZMod 2) K U) (B : Subgroup K) (W : Submodule (ZMod 2) U)
    (hindex : Odd B.index)
    (hquot : ∀ (g : K) (u : U), ρ g u - u ∈ W)
    (hfixed : W ⊓ fixedSpace ρ B ≤ ρ.invariants) :
    fixedSpace ρ B = ρ.invariants := by
  classical
  let : B.FiniteIndex := ⟨by obtain ⟨n, hn⟩ := hindex; omega⟩
  let := Fintype.ofFinite (K ⧸ B)
  apply le_antisymm
  · intro u hu
    change ∀ b : B, ρ b u = u at hu
    let f : K ⧸ B → U := fun q => ρ q.out u
    have hf (g : K) : f (QuotientGroup.mk g) = ρ g u := by
      obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul B g
      change ρ (QuotientGroup.mk g : K ⧸ B).out u = _
      rw [hb, map_mul, Module.End.mul_apply, hu b]
    have hcov (g : K) (q : K ⧸ B) : f (g • q) = ρ g (f q) := by
      induction q using Quotient.inductionOn with
      | h a =>
        change f (QuotientGroup.mk (g * a)) = _
        rw [hf, hf, map_mul, Module.End.mul_apply]
    let v : U := ∑ q, f q
    have hv : v ∈ ρ.invariants := by
      intro g
      change ρ g (∑ q, f q) = ∑ q, f q
      rw [map_sum]
      simp_rw [← hcov]
      exact Equiv.sum_comp (MulAction.toPerm g) f
    have hodd : (Fintype.card (K ⧸ B) : ZMod 2) = 1 := by
      have hc : Odd (Fintype.card (K ⧸ B)) := by
        simpa only [Subgroup.index, Nat.card_eq_fintype_card] using hindex
      obtain ⟨n, hn⟩ := hc
      rw [hn]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]
    have hdiff : v - u ∈ W := by
      have hsum : (∑ q : K ⧸ B, u) = u := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (ZMod 2), hodd,
          one_smul]
      rw [show v - u = ∑ q : K ⧸ B, (f q - u) by rw [Finset.sum_sub_distrib, hsum]]
      exact W.sum_mem (fun q _ => hquot q.out u)
    have hdiffB : v - u ∈ fixedSpace ρ B := by
      intro b
      change ρ b (v - u) = v - u
      rw [map_sub, hv b, hu b]
    have hdiffK := hfixed ⟨hdiff, hdiffB⟩
    intro g
    have hh := hdiffK g
    rw [map_sub, hv g] at hh
    exact (sub_right_inj.mp hh)
  · intro u hu b
    exact hu b

/-- Two noncentral layers above a central layer, followed by a central quotient.
Each layer containment can be supplied by an equivariant section calculation. -/
theorem odd_index_fixedSpace_extension_two_layers
    (ρ : Representation (ZMod 2) K U) (B : Subgroup K)
    (C D W : Submodule (ZMod 2) U) (hindex : Odd B.index)
    (hquot : ∀ (g : K) (u : U), ρ g u - u ∈ W)
    (hcentral : C ≤ ρ.invariants)
    (hfirst : D ⊓ fixedSpace ρ B ≤ C)
    (hsecond : W ⊓ fixedSpace ρ B ≤ D) :
    fixedSpace ρ B = ρ.invariants := by
  apply odd_index_fixedSpace_extension ρ B W hindex hquot
  intro u hu
  exact hcentral (hfirst ⟨hsecond hu, hu.2⟩)
end Representation.HigherFieldBorelFixedSpaces
namespace Representation.HigherFieldBorelFixedSpaces
open Representation.BinaryOffender
variable {K U V : Type*} [Group K] [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Fixed-space passage through an actual equivariant linear map. -/
theorem fixedSpace_eq_bot_of_map
    (ρ : Representation (ZMod 2) K U) (σ : Representation (ZMod 2) K V)
    (B : Subgroup K) (f : U →ₗ[ZMod 2] V)
    (he : ∀ (b : B) (u : U), f (ρ b u) = σ b (f u))
    (htarget : fixedSpace σ B = ⊥)
    (hkernel : f.ker ⊓ fixedSpace ρ B = ⊥) : fixedSpace ρ B = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro u hu
  have hm : f u ∈ fixedSpace σ B := by
    intro b
    change σ b (f u) = f u
    rw [← he]
    exact congrArg f (hu b)
  have hz : f u = 0 := by rwa [htarget, Submodule.mem_bot] at hm
  have hk : u ∈ f.ker ⊓ fixedSpace ρ B := ⟨hz, hu⟩
  rwa [hkernel, Submodule.mem_bot] at hk

/-- Section coordinates with an explicit kernel and actor map suffice for
fixed vectors to lie in the lower submodule. -/
theorem fixedSpace_le_of_section
    {L : Type*} [Group L]
    (ρ : Representation (ZMod 2) K U) (σ : Representation (ZMod 2) L V)
    (B : Subgroup K) (C D : Submodule (ZMod 2) U)
    (hD : ∀ (b : B) (d : D), ρ b d ∈ D)
    (actor : B →* L) (e : (D ⧸ C.comap D.subtype) ≃ₗ[ZMod 2] V)
    (he : ∀ (b : B) (d : D),
      e (Submodule.Quotient.mk (⟨ρ b d, hD b d⟩ : D)) =
        σ (actor b) (e (Submodule.Quotient.mk d)))
    (hzero : ∀ v : V, (∀ b : B, σ (actor b) v = v) → v = 0) :
    D ⊓ fixedSpace ρ B ≤ C := by
  intro u hu
  let d : D := ⟨u, hu.1⟩
  have hz : e (Submodule.Quotient.mk d) = 0 := by
    apply hzero
    intro b
    rw [← he]
    congr 2
    exact Subtype.ext (hu.2 b)
  have hq : (Submodule.Quotient.mk d : D ⧸ C.comap D.subtype) = 0 :=
    e.injective (hz.trans e.map_zero.symm)
  change d ∈ C.comap D.subtype
  exact (Submodule.Quotient.mk_eq_zero _).mp hq
end Representation.HigherFieldBorelFixedSpaces

namespace Representation.HigherFieldBorelFixedSpaces
open Representation.BinaryOffender
variable {K L U V : Type*} [Group K] [Group L]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup V] [Module (ZMod 2) V]

/-- A surjective image of the specified actor subgroup and genuine quotient
coordinates turn the concrete model calculation into a section containment. -/
theorem fixedSpace_le_of_model_section
    (ρ : Representation (ZMod 2) K U) (σ : Representation (ZMod 2) L V)
    (B : Subgroup K) (B₀ : Subgroup L) (C D : Submodule (ZMod 2) U)
    (hD : ∀ (b : B) (d : D), ρ b d ∈ D)
    (actor : B →* L) (hactor : actor.range = B₀)
    (e : (D ⧸ C.comap D.subtype) ≃ₗ[ZMod 2] V)
    (he : ∀ (b : B) (d : D),
      e (Submodule.Quotient.mk (⟨ρ b d, hD b d⟩ : D)) =
        σ (actor b) (e (Submodule.Quotient.mk d)))
    (hzero : fixedSpace σ B₀ = ⊥) : D ⊓ fixedSpace ρ B ≤ C := by
  apply fixedSpace_le_of_section ρ σ B C D hD actor e he
  intro v hv
  have hm : v ∈ fixedSpace σ B₀ := by
    intro b
    have hb : b.val ∈ actor.range := hactor.symm ▸ b.property
    obtain ⟨a, ha⟩ := hb
    change σ b v = v
    rw [← ha]
    exact hv a
  rwa [hzero, Submodule.mem_bot] at hm

/-- The section calculation and odd-index averaging combine without assuming
that the module extension splits. -/
theorem odd_index_fixedSpace_extension_of_model_section
    (ρ : Representation (ZMod 2) K U) (σ : Representation (ZMod 2) L V)
    (B : Subgroup K) (B₀ : Subgroup L) (C W : Submodule (ZMod 2) U)
    (hindex : Odd B.index)
    (hquot : ∀ (g : K) (u : U), ρ g u - u ∈ W)
    (hcentral : C ≤ ρ.invariants)
    (hW : ∀ (b : B) (w : W), ρ b w ∈ W)
    (actor : B →* L) (hactor : actor.range = B₀)
    (e : (W ⧸ C.comap W.subtype) ≃ₗ[ZMod 2] V)
    (he : ∀ (b : B) (w : W),
      e (Submodule.Quotient.mk (⟨ρ b w, hW b w⟩ : W)) =
        σ (actor b) (e (Submodule.Quotient.mk w)))
    (hzero : fixedSpace σ B₀ = ⊥) : fixedSpace ρ B = ρ.invariants :=
  odd_index_fixedSpace_extension ρ B W hindex hquot
    ((fixedSpace_le_of_model_section ρ σ B B₀ C W hW actor hactor e he hzero).trans hcentral)
end Representation.HigherFieldBorelFixedSpaces
