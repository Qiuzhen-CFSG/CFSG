module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Tactic.Abel

/-!
# Two copies of an involution fixed space in characteristic two

If `t² = 1` and `t s = t + s t`, the space is the direct sum of the
`t`-fixed space `W` and its image under `s`. The explicit coordinates are
`(x + s (x + t x), x + t x)`, with inverse `(u,v) ↦ u + s v`.
Every operator commuting with `t` and `s` acts diagonally in these coordinates.

The relations arise from a norm-zero binary S₃-module, with `s` the inverse
of an element of order three. Source application: Aschbacher–Smith,
combined manuscript (1 March 2004), printed p.1153, proof of 15.3.67.
-/

@[expose] public section

namespace Representation.BinaryInvolutionPairing
variable {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]

lemma add_self (x : X) : x + x = 0 := by
  have h := @two_smul (ZMod 2) X _ _ _ x
  rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
  exact h.symm

variable (W : Submodule (ZMod 2) X) (t s : Module.End (ZMod 2) X)
  (hW : ∀ x, x ∈ W ↔ t x = x) (ht : ∀ x, t (t x) = x)
  (hts : ∀ x, t (s x) = t x + s (t x))

include hW ht in
lemma second_mem (x : X) : x + t x ∈ W := by
  rw [hW, map_add, ht, add_comm]

include hW ht hts in
lemma first_mem (x : X) : x + s (x + t x) ∈ W := by
  rw [hW, map_add, hts, map_add, ht]
  have hh := add_self (t x)
  abel_nf at hh ⊢
  rw [hh, zero_add]

noncomputable def coordinates : X →ₗ[ZMod 2] W × W :=
  ((1 + s * (1 + t)).codRestrict W (first_mem W t s hW ht hts)).prod
    ((1 + t).codRestrict W (second_mem W t hW ht))

noncomputable def assemble : W × W →ₗ[ZMod 2] X :=
  W.subtype.comp (LinearMap.fst _ _ _) +
    s.comp (W.subtype.comp (LinearMap.snd _ _ _))

lemma coordinates_assemble (w : W × W) :
    coordinates W t s hW ht hts (assemble W s w) = w := by
  have h₁ := (hW (w.1 : X)).mp w.1.property
  have h₂ := (hW (w.2 : X)).mp w.2.property
  have he : ((w.1 : X) + s w.2) + t ((w.1 : X) + s w.2) = w.2 := by
    rw [map_add, hts, h₁, h₂]
    have h₃ := add_self (w.1 : X)
    have h₄ := add_self (s (w.2 : X))
    abel_nf at h₃ h₄ ⊢
    rw [h₃, h₄]
    simp
  apply Prod.ext <;> apply Subtype.ext
  · change (w.1 : X) + s w.2 + s (((w.1 : X) + s w.2) + t ((w.1 : X) + s w.2)) = w.1
    rw [he, add_assoc, add_self, add_zero]
  · exact he

lemma assemble_coordinates (x : X) :
    assemble W s (coordinates W t s hW ht hts x) = x := by
  change x + s (x + t x) + s (x + t x) = x
  rw [add_assoc, add_self, add_zero]

noncomputable def equiv : X ≃ₗ[ZMod 2] W × W :=
  LinearEquiv.ofLinearMap (coordinates W t s hW ht hts) (assemble W s)
    (LinearMap.ext (coordinates_assemble W t s hW ht hts))
    (LinearMap.ext (assemble_coordinates W t s hW ht hts))

lemma equiv_apply (x : X) :
    equiv W t s hW ht hts x =
      (⟨x + s (x + t x), first_mem W t s hW ht hts x⟩,
       ⟨x + t x, second_mem W t hW ht x⟩) := rfl

lemma equiv_symm_apply (w : W × W) :
    (equiv W t s hW ht hts).symm w = (w.1 : X) + s w.2 := rfl

lemma equiv_equivariant (c : Module.End (ZMod 2) X)
    (hcW : ∀ w ∈ W, c w ∈ W)
    (hct : ∀ x, t (c x) = c (t x)) (hcs : ∀ x, s (c x) = c (s x)) (x : X) :
    equiv W t s hW ht hts (c x) =
      ((c.restrict hcW) (equiv W t s hW ht hts x).1,
       (c.restrict hcW) (equiv W t s hW ht hts x).2) := by
  apply Prod.ext <;> apply Subtype.ext
  · change c x + s (c x + t (c x)) = c (x + s (x + t x))
    simp only [map_add, hct, hcs]
  · change c x + t (c x) = c (x + t x)
    rw [hct, map_add]

include hW ht hts in
lemma sup_map_eq_top : W ⊔ W.map s = ⊤ := by
  apply top_unique
  intro x _
  let w := equiv W t s hW ht hts x
  have hx : (w.1 : X) + s w.2 = x := (equiv W t s hW ht hts).symm_apply_apply x
  rw [← hx]
  exact Submodule.add_mem_sup w.1.property ⟨w.2, w.2.property, rfl⟩

include hW hts in
lemma inf_map_eq_bot : W ⊓ W.map s = ⊥ := by
  apply bot_unique
  rintro x ⟨hx, z, hz, rfl⟩
  have h₁ := (hW _).mp hx
  have h₂ := (hW _).mp hz
  rw [hts, h₂] at h₁
  have hz0 : z = 0 := by
    have hh := congrArg (fun v => v - s z) h₁
    simpa using hh
  simp [hz0]
end Representation.BinaryInvolutionPairing
