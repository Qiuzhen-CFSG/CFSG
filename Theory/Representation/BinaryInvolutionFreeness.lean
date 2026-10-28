module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Freeness in binary involution modules

A nonidentity involution on a binary plane has the same fixed and displacement
spaces, by rank-nullity. An extension of two free involution modules is free:
first lift a displacement in the quotient, then correct the remaining fixed
vector in the kernel. The statements use an arbitrary acting monoid and the
actual intertwining map, with no semisimplicity or splitting assumption.

Application: Q/U with kernel HC/U and natural quotient Q/HC in
`CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.ModuleActions.Extension`.
Source: Aschbacher–Smith, J.2.6, printed p.435 (PDF p.446).
-/

public section

open Representation
namespace Representation.BinaryInvolution
variable {Γ : Type*} [Monoid Γ]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private theorem binary_add_self (v : W) : v + v = 0 := by
  have h := @two_smul (ZMod 2) W _ _ _ v
  rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
  exact h.symm

private theorem binary_neg (v : W) : -v = v :=
  neg_eq_of_add_eq_zero_left (binary_add_self v)

theorem free_of_finrank_two [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) Γ W) (t : Γ)
    (ht : t * t = 1) (hdim : Module.finrank (ZMod 2) W = 2)
    (hne : ∃ v, ρ t v ≠ v) : (∀ v, ρ t v = v → ∃ w, ρ t w + w = v) := by
  let D := ρ t - 1
  have hincl : D.range ≤ D.ker := by
    rintro _ ⟨w, rfl⟩
    change ρ t (ρ t w - w) - (ρ t w - w) = 0
    have haa : ρ t (ρ t w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, ht, map_one, Module.End.one_apply]
    rw [map_sub, haa]
    calc
      w - ρ t w - (ρ t w - w) = (w + w) - (ρ t w + ρ t w) := by abel
      _ = 0 := by rw [binary_add_self, binary_add_self, sub_self]
  have hr0 : Module.finrank (ZMod 2) D.range ≠ 0 := by
    intro h
    have hz : D = 0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h)
    obtain ⟨v, hv⟩ := hne
    exact hv (LinearMap.congr_fun (sub_eq_zero.mp hz) v)
  have hdim' := D.finrank_range_add_finrank_ker
  rw [hdim] at hdim'
  have he : D.range = D.ker := Submodule.eq_of_le_of_finrank_eq hincl
    (by have := Submodule.finrank_mono hincl; omega)
  intro v hv
  have hvk : v ∈ D.ker := by change ρ t v - v = 0; rw [hv, sub_self]
  obtain ⟨w, hw⟩ := he.symm ▸ hvk
  refine ⟨w, ?_⟩
  change ρ t w - w = v at hw
  simpa only [sub_eq_add_neg, binary_neg] using hw

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem free_of_free_kernel_and_quotient
    (ρ : Representation (ZMod 2) Γ W) (σ : Representation (ZMod 2) Γ V)
    (p : W →ₗ[ZMod 2] V) (hp : Function.Surjective p)
    (heq : ∀ g v, p (ρ g v) = σ g (p v))
    (t : Γ) (ht : t * t = 1) (hquot : ∀ v, σ t v = v → ∃ w, σ t w + w = v)
    (hker : ∀ v ∈ p.ker, ρ t v = v → ∃ w ∈ p.ker, ρ t w + w = v) :
    (∀ v, ρ t v = v → ∃ w, ρ t w + w = v) := by
  intro v hv
  obtain ⟨b, hb⟩ := hquot (p v) (by rw [← heq, hv])
  obtain ⟨w, hw⟩ := hp b
  let c := v - (ρ t w + w)
  have hc : c ∈ p.ker := by
    change p (v - (ρ t w + w)) = 0
    rw [map_sub, map_add, heq, hw, hb, sub_self]
  have hcc : ρ t c = c := by
    have htw : ρ t (ρ t w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, ht, map_one, Module.End.one_apply]
    dsimp [c]
    rw [map_sub, map_add, hv, htw, add_comm w]
  obtain ⟨u, _, hu⟩ := hker c hc hcc
  refine ⟨w + u, ?_⟩
  rw [map_add]
  calc
    ρ t w + ρ t u + (w + u) = (ρ t w + w) + (ρ t u + u) := by abel
    _ = v := by rw [hu]; dsimp [c]; abel

end Representation.BinaryInvolution
