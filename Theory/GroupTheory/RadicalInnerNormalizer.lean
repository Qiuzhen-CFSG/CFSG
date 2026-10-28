module
public import Theory.GroupTheory.SaturatedCentralProjection
public import Theory.GroupTheory.PRadical
public import Theory.GroupTheory.RadicalNormalizerControl
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-!
# Radical intersections under inner actions

If a radical p-subgroup R acts by inner automorphisms on a normal subgroup
K whose center is a p-group, saturation puts the K-coordinate of every
element of R back in R. Thus R is the product of R intersect K and its
centralizer of K. The normalizer in K of the first factor normalizes R.

This retains the central overlap, and does not require a Sylow subgroup
of K in R. It supplies the central-cover normalizer lift in the original
unitary Rudvalis pushing-up argument.
Source: Aschbacher--Smith C.2.2(1), printed p.144, and 4.2.13, pp.611--612.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Radical saturation splits an inner-acting prime subgroup over its actual intersection. -/
theorem radical_eq_inf_sup_centralizer (K R : Subgroup G) [K.Normal]
    (hR : IsPRadical p R) (hZ : IsPGroup p (center K))
    (hi : R ≤ K ⊔ centralizer (K : Set G)) :
    R = (R ⊓ K) ⊔ (R ⊓ centralizer (K : Set G)) := by
  have hs := inf_sup_centralizer_eq_inf_of_saturation K (normalizer (R : Set G)) R
    hZ hR.isPGroup le_rfl (fun P hp hn =>
      le_of_normalizer_le_normalizer_of_pCore_normalizer_le R P hR.isPGroup hp hR.2.le hn)
  apply le_antisymm _ (sup_le inf_le_left inf_le_left)
  intro r hr
  have hm : r ∈ (K : Set G) * (centralizer (K : Set G) : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right K _ le_normalizer_of_normal]
    exact hi hr
  obtain ⟨k,hk,c,hc,rfl⟩ := hm
  have hkR : k ∈ R := by
    have hkS : k ∈ K ⊓ (R ⊔ centralizer (K : Set G)) := by
      refine ⟨hk,?_⟩
      have hh := (R ⊔ centralizer (K : Set G)).mul_mem
        (mem_sup_left hr) (mem_sup_right ((centralizer _).inv_mem hc))
      change k ∈ R ⊔ centralizer (K : Set G)
      simpa only [mul_inv_cancel_right] using hh
    exact (hs ▸ hkS).2
  have hcR : c ∈ R := by
    simpa only [inv_mul_cancel_left] using R.mul_mem (R.inv_mem hkR) hr
  exact mul_mem (mem_sup_left ⟨hkR,hk⟩) (mem_sup_right ⟨hcR,hc⟩)

/-- The intrinsic intersection normalizer preserves the entire original radical. -/
theorem radical_intersection_normalizer_le (K R : Subgroup G) [K.Normal]
    (hR : IsPRadical p R) (hZ : IsPGroup p (center K))
    (hi : R ≤ K ⊔ centralizer (K : Set G)) :
    K ⊓ normalizer (R ⊓ K : Set G) ≤ normalizer (R : Set G) := by
  have he := radical_eq_inf_sup_centralizer K R hR hZ hi
  have hc : K ≤ normalizer (R ⊓ centralizer (K : Set G) : Set G) :=
    (le_centralizer_iff.mp (show R ⊓ centralizer (K : Set G) ≤
      centralizer (K : Set G) from inf_le_right)).trans (centralizer_le_normalizer _)
  intro x hx
  have hn : x ∈ normalizer (((R ⊓ K) ⊔ (R ⊓ centralizer (K : Set G)) : Subgroup G) : Set G) :=
    normalizer_inf_normalizer_le_normalizer_sup (R ⊓ K)
      (R ⊓ centralizer (K : Set G)) ⟨hx.2,hc hx.1⟩
  exact he.symm ▸ hn

end Theory.GroupTheory
