module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel

/-!
# Fixed spaces of an involution inverting a cubic operator

For a binary module, `t²+t+1=0`, `b²=1` and `bt=t²b` imply
`X = C_X(b) ⊕ t C_X(b)`. The explicit decomposition is obtained from
`v=x+bx` and `u=x+tv`. Moreover, every b-fixed vector is the displacement
of its t-translate. This gives fixed-representative lifting through any
compatible quotient whose kernel is t-invariant.

The decomposition argument generalizes the private four-dimensional calculation
in `Theory.Representation.InvertedThreeCentralizer`. The lifting statement does
not silently identify the image of fixed vectors with quotient fixed vectors.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.3.67, printed p.1153, PDF p.1170.
-/

@[expose] public section

namespace Representation.InvertedThreeFixed
variable {X W : Type*} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup W] [Module (ZMod 2) W]

private theorem twice (x : X) : x + x = 0 := by
  have h := @two_smul (ZMod 2) X _ _ _ x
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo, zero_smul] at h
  exact h.symm

/-- Explicit decomposition into a fixed vector and a cubic translate of one. -/
theorem fixed_decomposition (t b : Module.End (ZMod 2) X)
    (ht : t ^ 2 + t + 1 = 0) (hb : b * b = 1)
    (hbt : b * t = t ^ 2 * b) :
    ∀ x : X, ∃ u v : X, b u = u ∧ b v = v ∧ x = u + t v := by
  have hquad (x : X) : t (t x) + t x + x = 0 := LinearMap.congr_fun ht x
  have hbb (x : X) : b (b x) = x := LinearMap.congr_fun hb x
  have hbt' (x : X) : b (t x) = t (t (b x)) := LinearMap.congr_fun hbt x
  have hsum (x : X) : t (t x) + t x = x := by
    exact add_right_cancel (show (t (t x) + t x) + x = x + x by
      rw [hquad, twice])
  intro x
  let v := x + b x
  have hv : b v = v := by simp [v, hbb, add_comm]
  refine ⟨x + t v, v, ?_, hv, ?_⟩
  · rw [map_add, hbt', hv]
    have hh : t (t v) = v + t v := by
      apply add_right_cancel (b := t v)
      rw [hsum]
      simp only [add_assoc, twice, add_zero]
    rw [hh]
    dsimp [v]
    calc
      b x + (x + b x + t (x + b x)) =
          x + t (x + b x) + (b x + b x) := by abel
      _ = x + t (x + b x) := by rw [twice, add_zero]
  · rw [add_assoc, twice, add_zero]

/-- The two displayed summands are complementary in every dimension. -/
theorem isCompl_fixed_map (t b : Module.End (ZMod 2) X)
    (ht : t ^ 2 + t + 1 = 0) (hb : b * b = 1)
    (hbt : b * t = t ^ 2 * b) :
    IsCompl (LinearMap.ker (b - 1)) ((LinearMap.ker (b - 1)).map t) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hx hx'
    obtain ⟨v, hv, rfl⟩ := hx'
    have hv' : b v = v := sub_eq_zero.mp hv
    have hx' : b (t v) = t v := sub_eq_zero.mp hx
    have he : t (t v) = t v := by
      have h := LinearMap.congr_fun hbt v
      change b (t v) = t (t (b v)) at h
      rw [hv', hx'] at h
      exact h.symm
    have hz : v = 0 := by
      have h : t (t v) + t v + v = 0 := LinearMap.congr_fun ht v
      rwa [he, twice, zero_add] at h
    rw [hz, map_zero]
  · apply codisjoint_iff.mpr
    apply top_unique
    intro x _
    obtain ⟨u, v, hu, hv, rfl⟩ := fixed_decomposition t b ht hb hbt x
    exact Submodule.mem_sup.mpr ⟨u, sub_eq_zero.mpr hu, t v,
      ⟨v, sub_eq_zero.mpr hv, rfl⟩, rfl⟩

/-- An involutory action lifts fixed vectors if its kernel fixed vectors are displacements. -/
theorem exists_fixed_lift (s : Module.End (ZMod 2) X)
    (t : Module.End (ZMod 2) W) (q : X →ₗ[ZMod 2] W)
    (hq : Function.Surjective q) (heq : ∀ x, q (s x) = t (q x))
    (hs : s * s = 1)
    (hker : ∀ e ∈ q.ker, s e = e → ∃ d ∈ q.ker, s d - d = e)
    (w : W) (hw : t w = w) : ∃ v : X, s v = v ∧ q v = w := by
  obtain ⟨x, rfl⟩ := hq w
  have hδ : s x - x ∈ q.ker := by
    change q (s x - x) = 0
    rw [map_sub, heq, hw, sub_self]
  have hfix : s (s x - x) = s x - x := by
    rw [map_sub, show s (s x) = x from LinearMap.congr_fun hs x]
    have hn (a : X) : -a = a := neg_eq_iff_add_eq_zero.mpr (twice a)
    simp only [sub_eq_add_neg, hn, add_comm]
  obtain ⟨d, hd, hdx⟩ := hker _ hδ hfix
  refine ⟨x - d, ?_, ?_⟩
  · rw [map_sub]
    apply sub_eq_sub_iff_add_eq_add.mpr
    exact (sub_eq_sub_iff_add_eq_add.mp hdx).symm.trans (add_comm _ _)
  · rw [map_sub, show q d = 0 from hd, sub_zero]

/-- A fixed vector is the displacement of its cubic translate. -/
theorem fixed_displacement (t b : Module.End (ZMod 2) X)
    (ht : t ^ 2 + t + 1 = 0) (hbt : b * t = t ^ 2 * b)
    (x : X) (hx : b x = x) : b (t x) - t x = x := by
  have h : b (t x) = t (t x) := by
    have h := LinearMap.congr_fun hbt x
    change b (t x) = t (t (b x)) at h
    rwa [hx] at h
  rw [h]
  have hquad : t (t x) + t x + x = 0 := LinearMap.congr_fun ht x
  have hn : -(t x) = t x := neg_eq_iff_add_eq_zero.mpr (twice _)
  rw [sub_eq_add_neg, hn]
  exact add_right_cancel (show (t (t x) + t x) + x = x + x by
    rw [hquad, twice])

end Representation.InvertedThreeFixed
