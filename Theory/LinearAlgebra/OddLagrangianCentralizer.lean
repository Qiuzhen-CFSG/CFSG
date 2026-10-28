module
public import Theory.LinearAlgebra.AlternatingFinrank
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

/-!
# Centralizers of transitive actions on odd binary Lagrangians

An isometry fixing a Lagrangian pointwise has displacement into that
Lagrangian. If it centralizes an action transitive on the nonzero vectors,
a nonzero displacement has full image. Its symmetric displacement form has
zero diagonal: the diagonal represents a fixed vector in the Lagrangian.
It is therefore alternating, whose rank is even. An odd Lagrangian
dimension forces the displacement to vanish.

This isolates the linear algebra used to prove that the original plane
vertex in Aschbacher–Smith I.5 has trivial center, as required in 13.7.5–6.
-/

public noncomputable section
namespace Theory.LinearAlgebra
open LinearMap
open scoped BilinForm
variable {V H : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable [Group H]

/-- In a binary symplectic space, an isometry fixing an odd-dimensional
Lagrangian pointwise and centralizing a transitive linear action on its
nonzero vectors is the identity. -/
theorem centralizer_eq_one_of_odd_lagrangian
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate) (hA : B.IsAlt)
    (W : Submodule (ZMod 2) V) (hW : B.orthogonal W = W)
    (hodd : Odd (Module.finrank (ZMod 2) W)) (hdim : 1 < Module.finrank (ZMod 2) W)
    (ρ : H →* (V ≃ₗ[ZMod 2] V))
    (hρ : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (htrans : ∀ v ∈ W, v ≠ 0 → ∀ w ∈ W, w ≠ 0 → ∃ g : H, ρ g v = w)
    (c : V ≃ₗ[ZMod 2] V) (hc : ∀ x y, B (c x) (c y) = B x y)
    (hfix : ∀ w ∈ W, c w = w) (hcomm : ∀ g x, c (ρ g x) = ρ g (c x)) : c = 1 := by
  have hsym (x y : V) : B x y = B y x := by
    simpa only [CharTwo.neg_eq] using hA.neg_eq x y
  let N : V →ₗ[ZMod 2] V := c.toLinearMap - LinearMap.id
  have hN (x : V) : N x = c x - x := rfl
  have hN0 (x : V) (hx : x ∈ W) : N x = 0 := by rw [hN, hfix x hx, sub_self]
  have hrange (x : V) : N x ∈ W := by
    rw [← hW]
    intro w hw
    have h := hc w x
    rw [hfix w hw] at h
    change B w (c x - x) = 0
    rw [map_sub, h, sub_self]
  have hiso {x y : V} (hx : x ∈ W) (hy : y ∈ W) : B x y = 0 :=
    (show y ∈ B.orthogonal W from hW.symm ▸ hy) x hx
  have hcommN (g : H) (x : V) : N (ρ g x) = ρ g (N x) := by
    simp only [hN, hcomm, map_sub]
  have hselfadj (x y : V) : B (N x) y = B x (N y) := by
    have hh := hc x y
    have hx : c x = N x + x := by rw [hN]; abel
    have hy : c y = N y + y := by rw [hN]; abel
    rw [hx, hy] at hh
    simp only [map_add, LinearMap.add_apply, hiso (hrange x) (hrange y), zero_add] at hh
    have he : B (N x) y + B x (N y) = 0 := by linear_combination hh
    exact (eq_neg_iff_add_eq_zero.mpr he).trans (CharTwo.neg_eq _)
  let C : LinearMap.BilinForm (ZMod 2) V := B.compLeft N
  have hC (x y : V) : C x y = B (N x) y := rfl
  have hCsym (x y : V) : C x y = C y x := by rw [hC, hC, hselfadj, hsym]
  let δ : V →ₗ[ZMod 2] ZMod 2 := {
    toFun := fun x => C x x
    map_add' x y := by
      simp only [map_add, LinearMap.add_apply, hCsym y x]
      ring_nf
      simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
    map_smul' a x := by
      have ha : a = 0 ∨ a = 1 := by decide +revert
      rcases ha with rfl | rfl <;> simp }
  have hδ (g : H) (x : V) : δ (ρ g x) = δ x := by
    change B (N (ρ g x)) (ρ g x) = B (N x) x
    rw [hcommN, hρ]
  let v := (B.toDual hB).symm δ
  have hv (x : V) : B v x = δ x := B.apply_toDual_symm_apply δ x
  have hvW : v ∈ W := by
    rw [← hW]
    intro w hw
    rw [hsym, hv]
    change B (N w) w = 0
    rw [hN0 w hw, map_zero, LinearMap.zero_apply]
  have hvfixed (g : H) : ρ g v = v := by
    apply sub_eq_zero.mp
    apply hB.1
    intro x
    rw [map_sub, LinearMap.sub_apply]
    apply sub_eq_zero.mpr
    obtain ⟨y, rfl⟩ := (ρ g).surjective x
    rw [hρ, hv, hv, hδ]
  have hvzero : v = 0 := by
    by_contra hvne
    have hle : W ≤ Submodule.span (ZMod 2) {v} := by
      intro w hw
      by_cases hw0 : w = 0
      · exact hw0 ▸ Submodule.zero_mem _
      obtain ⟨g, hg⟩ := htrans v hvW hvne w hw hw0
      rw [← hg, hvfixed]
      exact Submodule.subset_span (Set.mem_singleton v)
    have hh := Submodule.finrank_mono hle
    rw [finrank_span_singleton hvne] at hh
    omega
  have hCalt : C.IsAlt := by
    intro x
    change δ x = 0
    rw [← hv, hvzero, map_zero, LinearMap.zero_apply]
  by_cases hNzero : N = 0
  · apply LinearEquiv.ext
    intro x
    change c x = x
    have h := congrArg (fun f : V →ₗ[ZMod 2] V => f x) hNzero
    exact sub_eq_zero.mp h
  have hfull : N.range = W := by
    apply le_antisymm
    · rintro w ⟨x, rfl⟩
      exact hrange x
    obtain ⟨x, hx⟩ : ∃ x : V, N x ≠ 0 := by
      by_contra! h
      exact hNzero (LinearMap.ext h)
    intro w hw
    by_cases hw0 : w = 0
    · exact hw0 ▸ Submodule.zero_mem _
    obtain ⟨g, hg⟩ := htrans (N x) (hrange x) hx w hw hw0
    exact ⟨ρ g x, (hcommN g x).trans hg⟩
  have hker : C.ker = N.ker := by
    ext x
    constructor
    · intro hx
      apply hB.1
      intro y
      exact congrArg (fun f : V →ₗ[ZMod 2] ZMod 2 => f y) hx
    · intro hx
      apply LinearMap.ext
      intro y
      change B (N x) y = 0
      rw [hx, map_zero, LinearMap.zero_apply]
  have he := AlternatingForm.even_finrank_sub_finrank_ker C hCalt
  have hd := N.finrank_range_add_finrank_ker
  rw [hfull] at hd
  rw [hker, ← hd, Nat.add_sub_cancel_right] at he
  exfalso
  exact (Nat.not_even_iff_odd.mpr hodd) he

end Theory.LinearAlgebra
