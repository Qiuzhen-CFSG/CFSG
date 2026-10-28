module

public import Mathlib.GroupTheory.Complement

/-!
# Normalizers and centralizers inside a split extension

Let L complement a normal subgroup Q and let Y ≤ L. The retraction onto L
sends N(Y) into N_L(Y). Its kernel in N(Y) centralizes Y, since the
retraction is the identity on Y. Consequently
N(Y) = N_L(Y) C_Q(Y), and similarly C(Y) = C_L(Y) C_Q(Y).

The application in Aschbacher, *Sporadic Groups* (1994), 47.2, printed
p.261, uses the literal A₅ complement and extraspecial core of C_G(z).
No coprimality, finiteness, or special group model is needed here.
-/

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]
private theorem complement_retraction (L Q : Subgroup G) [Q.Normal]
    (hc : L.IsComplement' Q) :
    ∃ f : G →* G, (∀ x, f x ∈ L) ∧ (∀ x ∈ L, f x = x) ∧ f.ker = Q := by
  let e := hc.QuotientMulEquiv
  let f := L.subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' Q))
  have he (x : L) : e.symm x = QuotientGroup.mk' Q (x : G) := rfl
  refine ⟨f, fun x => (e (QuotientGroup.mk' Q x)).property, ?_, ?_⟩
  · intro x hx
    change (e (QuotientGroup.mk' Q x) : G) = x
    rw [← he ⟨x, hx⟩, e.apply_symm_apply]
  · ext x
    change (e (QuotientGroup.mk' Q x) : G) = 1 ↔ x ∈ Q
    rw [← QuotientGroup.eq_one_iff x]
    constructor
    · intro hx
      apply e.injective
      exact (Subtype.ext hx).trans e.map_one.symm
    · intro hx
      change QuotientGroup.mk' Q x = 1 at hx
      rw [hx, e.map_one]
      rfl

private theorem retract_normalizes (L Y : Subgroup G) (hYL : Y ≤ L)
    (f : G →* G) (hf : ∀ x ∈ L, f x = x) {g : G}
    (hg : g ∈ normalizer (Y : Set G)) : f g ∈ normalizer (Y : Set G) := by
  have forward (a : G) (ha : a ∈ normalizer (Y : Set G)) (y : G) (hy : y ∈ Y) :
      f a * y * (f a)⁻¹ ∈ Y := by
    have hm := (mem_normalizer_iff.mp ha y).mp hy
    have he := hf _ (hYL hm)
    rw [map_mul, map_mul, map_inv, hf y (hYL hy)] at he
    exact he.symm ▸ hm
  apply mem_normalizer_iff.mpr
  intro y
  constructor
  · exact forward g hg y
  · intro hy
    have hh := forward g⁻¹ ((normalizer (Y : Set G)).inv_mem hg) _ hy
    simpa only [map_inv, inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel,
      mul_one] using hh

private theorem kernel_normalizer_centralizes (L Y : Subgroup G) (hYL : Y ≤ L)
    (f : G →* G) (hf : ∀ x ∈ L, f x = x) {g : G}
    (hg : g ∈ f.ker) (hn : g ∈ normalizer (Y : Set G)) :
    g ∈ centralizer (Y : Set G) := by
  apply mem_centralizer_iff.mpr
  intro y hy
  have he := hf _ (hYL ((mem_normalizer_iff.mp hn y).mp hy))
  rw [map_mul, map_mul, map_inv, show f g = 1 from hg,
    hf y (hYL hy), one_mul, inv_one, mul_one] at he
  exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm

public theorem IsComplement'.normalizer_eq_sup_centralizer (L Q Y : Subgroup G) [Q.Normal]
    (hc : L.IsComplement' Q) (hYL : Y ≤ L) :
    normalizer (Y : Set G) =
      (L ⊓ normalizer (Y : Set G)) ⊔ (Q ⊓ centralizer (Y : Set G)) := by
  obtain ⟨f, hfL, hf, hfQ⟩ := complement_retraction L Q hc
  apply le_antisymm
  · intro g hg
    have hfg := retract_normalizes L Y hYL f hf hg
    have hk : (f g)⁻¹ * g ∈ f.ker := by
      change f ((f g)⁻¹ * g) = 1
      rw [map_mul, map_inv, hf _ (hfL g), inv_mul_cancel]
    have hkN := (normalizer (Y : Set G)).mul_mem
      ((normalizer (Y : Set G)).inv_mem hfg) hg
    have hkC := kernel_normalizer_centralizes L Y hYL f hf hk hkN
    have hm := mul_mem_sup (show f g ∈ L ⊓ normalizer (Y : Set G) from ⟨hfL g, hfg⟩)
      (show (f g)⁻¹ * g ∈ Q ⊓ centralizer (Y : Set G) from ⟨hfQ ▸ hk, hkC⟩)
    simpa only [mul_inv_cancel_left] using hm
  · exact sup_le inf_le_right (inf_le_right.trans (centralizer_le_normalizer _))

public theorem IsComplement'.centralizer_eq_sup (L Q Y : Subgroup G) [Q.Normal]
    (hc : L.IsComplement' Q) (hYL : Y ≤ L) :
    centralizer (Y : Set G) =
      (L ⊓ centralizer (Y : Set G)) ⊔ (Q ⊓ centralizer (Y : Set G)) := by
  obtain ⟨f, hfL, hf, hfQ⟩ := complement_retraction L Q hc
  apply le_antisymm
  · intro g hg
    have hfg : f g ∈ centralizer (Y : Set G) := by
      apply mem_centralizer_iff.mpr
      intro y hy
      have he := congrArg f (mem_centralizer_iff.mp hg y hy)
      simpa only [map_mul, hf y (hYL hy)] using he
    have hk : (f g)⁻¹ * g ∈ f.ker := by
      change f ((f g)⁻¹ * g) = 1
      rw [map_mul, map_inv, hf _ (hfL g), inv_mul_cancel]
    have hkC := (centralizer (Y : Set G)).mul_mem
      ((centralizer (Y : Set G)).inv_mem hfg) hg
    have hm := mul_mem_sup (show f g ∈ L ⊓ centralizer (Y : Set G) from ⟨hfL g, hfg⟩)
      (show (f g)⁻¹ * g ∈ Q ⊓ centralizer (Y : Set G) from ⟨hfQ ▸ hk, hkC⟩)
    simpa only [mul_inv_cancel_left] using hm
  · exact sup_le inf_le_right inf_le_right
end Subgroup
