module

public import Theory.Representation.InvertedCubicTensor
public import Mathlib.LinearAlgebra.Projection

/-!
# Natural binary modules from two marked quadratic summands

Let a transposition fix A pointwise and have all displacements in A. If
A and one of its other S₃ translates are complementary, the braid relation
forces the natural transvection between them. The cubic subgroup then has
zero fixed space. The existing inverted-cubic tensor equivalence supplies
the direct sum of natural modules, while the original A is both the fixed
and displacement space of the specified transposition.

This is the field-exponent-one instance of Aschbacher–Smith G.2.3(6),
used in 12.8.9(2–3), printed pp.334 and853. No general natural-module
recognition theorem or semisimplicity assumption is required.
-/

namespace Representation.BinaryQuadraticPair

open InvertedCubicTensor
open scoped _root_.TensorProduct

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem quadratic_pair
    (t s : Module.End (ZMod 2) V) (A : Submodule (ZMod 2) V)
    (hs : s * s = 1) (hbraid : t * s * t = s * t * s)
    (hfix : ∀ a ∈ A, t a = a) (hr : LinearMap.range (t - 1) ≤ A)
    (hc : IsCompl A (A.map s)) :
    LinearMap.ker (t - 1) = A ∧ LinearMap.range (t - 1) = A ∧
      (A.map s).map (t - 1) = A ∧ (∀ x, (t * s) x = x → x = 0) := by
  let e := A.prodEquivOfIsCompl (A.map s) hc
  have hss (x : V) : s (s x) = x := LinearMap.congr_fun hs x
  have hstep (a : V) (ha : a ∈ A) : t (s a) = a + s a := by
    let w := t (s a) - s a
    have hw : w ∈ A := hr ⟨s a, rfl⟩
    have he : t (s a) = w + s a := (sub_add_cancel _ _).symm
    have hb : t (s a) = s (t (s a)) := by
      have hh := LinearMap.congr_fun hbraid a
      change t (s (t a)) = s (t (s a)) at hh
      rwa [hfix a ha] at hh
    have hh : w + s a = a + s w := by
      calc
        w + s a = t (s a) := he.symm
        _ = s (t (s a)) := hb
        _ = a + s w := by rw [he, map_add, hss]; exact add_comm _ _
    have hu := e.injective
      (show e (⟨w, hw⟩, ⟨s a, ⟨a, ha, rfl⟩⟩) =
        e (⟨a, ha⟩, ⟨s w, ⟨w, hw, rfl⟩⟩) from hh)
    have hwa : w = a := congrArg (fun p => ((p.1 : A) : V)) hu
    rw [he, hwa]
  have hdecomp (x : V) : ∃ a ∈ A, ∃ b ∈ A, x = a + s b := by
    have hx : x ∈ A ⊔ A.map s := hc.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨a, ha, y, hy, hxy⟩ := Submodule.mem_sup.mp hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a, ha, b, hb, hxy.symm⟩
  have hdelta (a : V) (ha : a ∈ A) (b : V) (hb : b ∈ A) :
      (t - 1) (a + s b) = b := by
    change t (a + s b) - (a + s b) = b
    rw [map_add, hfix a ha, hstep b hb]
    abel
  have hk : LinearMap.ker (t - 1) = A := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hdecomp x
      have hb0 : b = 0 := (hdelta a ha b hb).symm.trans hx
      simpa only [hb0, map_zero, add_zero] using ha
    · intro hx
      change t x - x = 0
      rw [hfix x hx, sub_self]
  have hmr : (A.map s).map (t - 1) = A := by
    apply le_antisymm
    · rintro _ ⟨x, _, rfl⟩
      exact hr ⟨x, rfl⟩
    · intro a ha
      refine ⟨s a, ⟨a, ha, rfl⟩, ?_⟩
      change t (s a) - s a = a
      rw [hstep a ha, add_sub_cancel_right]
  refine ⟨hk, le_antisymm hr ?_, hmr, ?_⟩
  · intro a ha
    obtain ⟨x, _, hx⟩ := hmr.symm ▸ ha
    exact ⟨x, hx⟩
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hdecomp x
    have hcalc : (t * s) (a + s b) = (a + b) + s a := by
      change t (s (a + s b)) = _
      rw [map_add, hss, map_add, hstep a ha, hfix b hb]
      abel
    have hh : (a + b) + s a = a + s b := hcalc.symm.trans hx
    have hu := e.injective
      (show e (⟨a + b, A.add_mem ha hb⟩, ⟨s a, ⟨a, ha, rfl⟩⟩) =
        e (⟨a, ha⟩, ⟨s b, ⟨b, hb, rfl⟩⟩) from hh)
    have hab : a + b = a := congrArg (fun p => ((p.1 : A) : V)) hu
    have hb0 : b = 0 := add_left_cancel (hab.trans (add_zero a).symm)
    have hsab : s a = s b := congrArg (fun p => ((p.2 : A.map s) : V)) hu
    have ha0 : a = 0 := by
      have hh := congrArg s hsab
      simpa only [hss, hb0] using hh
    simp only [ha0, hb0, map_zero, add_zero]

private theorem choose_other_inverter :
    ∀ t g : S₃, t * t = 1 → t ≠ 1 → g ≠ 1 → g ≠ t →
      ∃ s : S₃, s * s = 1 ∧ t * s * t = s * t * s ∧
        (t * s = cubic ∨ t * s = cubic * cubic) ∧ (s = g ∨ s = g * t) := by
  decide +kernel

/-- The quadratic action and two marked complementary translates give
the natural fixed and moved spaces and eliminate all cubic fixed vectors. -/
public theorem fixed_cubic_and_displacement
    (σ : Representation (ZMod 2) S₃ V) (A : Submodule (ZMod 2) V)
    (t g : S₃) (ht : t * t = 1) (ht1 : t ≠ 1)
    (hfix : ∀ a ∈ A, σ t a = a) (hr : LinearMap.range (σ t - 1) ≤ A)
    (hc : IsCompl A (A.map (σ g))) :
    (∀ v, σ cubic v = v → v = 0) ∧
      LinearMap.ker (σ t - 1) = A ∧ LinearMap.range (σ t - 1) = A ∧
      (A.map (σ g)).map (σ t - 1) = A := by
  have hAt : A.map (σ t) = A := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      rwa [hfix a ha]
    · intro a ha
      exact ⟨a, ha, hfix a ha⟩
  by_cases hg : g = 1 ∨ g = t
  · have hAg : A.map (σ g) = A := by
      rcases hg with rfl | rfl
      · rw [map_one]; exact Submodule.map_id A
      · exact hAt
    have hAA : IsCompl A A := by simpa only [hAg] using hc
    have hbot : A = ⊥ := by simpa only [inf_idem] using hAA.inf_eq_bot
    have htop : A = ⊤ := by simpa only [sup_idem] using hAA.sup_eq_top
    have hzero (v : V) : v = 0 := by
      have hv : v ∈ A := htop ▸ Submodule.mem_top
      simpa only [hbot, Submodule.mem_bot] using hv
    have hsame (B : Submodule (ZMod 2) V) : B = A := by
      ext v
      rw [hzero v]
      simp
    exact ⟨fun v _ => hzero v, hsame _, hsame _, hsame _⟩
  obtain ⟨s, hs, hbraid, hts, hsg⟩ := choose_other_inverter t g ht ht1
    (fun h => hg (Or.inl h)) (fun h => hg (Or.inr h))
  have hAs : A.map (σ s) = A.map (σ g) := by
    rcases hsg with rfl | rfl
    · rfl
    · rw [map_mul]
      change A.map ((σ g).comp (σ t)) = _
      rw [Submodule.map_comp, hAt]
  have hss : σ s * σ s = 1 := by rw [← map_mul, hs, map_one]
  have hb : σ t * σ s * σ t = σ s * σ t * σ s := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hbraid]
  obtain ⟨hk, hR, hB, hfree⟩ := quadratic_pair (σ t) (σ s) A hss hb hfix hr
    (hAs.symm ▸ hc)
  refine ⟨?_, hk, hR, hAs ▸ hB⟩
  intro v hv
  apply hfree v
  rw [← map_mul]
  rcases hts with h | h
  · rwa [h]
  · rw [h, map_mul, Module.End.mul_apply, hv, hv]

/-- The original marked quadratic configuration is a direct sum of the
concrete natural S₃ module; the equivalence intertwines the whole action. -/
public theorem natural_tensor_and_marks
    (σ : Representation (ZMod 2) S₃ V) (A : Submodule (ZMod 2) V)
    (t g : S₃) (ht : t * t = 1) (ht1 : t ≠ 1)
    (hfix : ∀ a ∈ A, σ t a = a) (hr : LinearMap.range (σ t - 1) ≤ A)
    (hc : IsCompl A (A.map (σ g))) :
    (∃ e : multiplicitySpace σ ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2] V,
      ∀ a z, e ((Representation.tprod (Representation.trivial (ZMod 2) S₃
          (multiplicitySpace σ)) (BinaryPermutation.coreRepresentation (Fin 3))) a z) =
        σ a (e z)) ∧
      LinearMap.ker (σ t - 1) = A ∧ LinearMap.range (σ t - 1) = A ∧
      (A.map (σ g)).map (σ t - 1) = A := by
  obtain ⟨hf, hk, hrange, hB⟩ := fixed_cubic_and_displacement σ A t g ht ht1 hfix hr hc
  refine ⟨⟨tensorEquiv σ hf, ?_⟩, hk, hrange, hB⟩
  intro a z
  induction z using _root_.TensorProduct.induction_on with
  | zero => simp
  | tmul i n =>
      simpa only [Representation.tprod_apply, _root_.TensorProduct.map_tmul,
        Representation.trivial_apply, Module.End.one_apply] using tensorEquiv_symmetric σ hf a i n
  | add x y hx hy => simp only [map_add, hx, hy]

end Representation.BinaryQuadraticPair
