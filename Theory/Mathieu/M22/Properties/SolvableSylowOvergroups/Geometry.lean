module

public import Theory.Mathieu.M22.Properties.FixedHexadLocal.KernelGeometry
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Geometry

/-!
# Uniqueness of a hexad containing its pointwise kernel

A nonidentity element of the elementary abelian pointwise kernel fixes exactly
the given hexad. Thus this order-sixteen group acts freely on the complement.
Every invariant set of fewer than sixteen points lies in the hexad; in
particular the invariant six-point set is unique. Consequently a subgroup
containing the kernel has its full design-automorphism normalizer in the same
hexad stabilizer.

This is the geometric normalizer step for Aschbacher–Smith 13.8.21(2),
printed p.956 (PDF p.973). Placement and kernel containment are explicit
hypotheses here and are not asserted by this module.
-/

public section

open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Mathieu.M22SolvableSylow

/-- A nonidentity hexad translation fixes exactly the hexad. -/
theorem kernel_fixed_iff {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    {u : M22} (hu : u ∈ m22HexadPointwiseKernel B) (hne : u ≠ 1) (a : Fin 22) :
    u • a = a ↔ a ∈ B := by
  let := m22HexadPointwiseKernel_elementaryAbelian hB
  have ho : orderOf u = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian u hu) hne
  obtain ⟨C, hC, hf⟩ := m22_exists_fixed_hexad u ho
  have hsub : B ⊆ C := fun b hb => (hf b).mp
    ((mem_m22HexadPointwiseKernel B u).mp hu b hb)
  have he : B = C := Finset.eq_of_subset_of_card_le hsub (by
    rw [m22Block_card B hB, m22Block_card C hC])
  simpa only [he] using hf a

/-- Every small invariant set of the pointwise kernel lies in its hexad. -/
theorem small_invariant_subset_hexad {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (S : Finset (Fin 22)) (hc : S.card < 16)
    (hs : m22HexadPointwiseKernel B ≤ stabilizer M22 S) : S ⊆ B := by
  classical
  intro a ha
  by_contra hnot
  let f : m22HexadPointwiseKernel B → S := fun u =>
    ⟨u.val • a, (mem_stabilizer_finset'.mp (hs u.property)) ha⟩
  have hi : Function.Injective f := by
    intro u v he
    have he' : u.val • a = v.val • a := congrArg Subtype.val he
    have hfix : (v.val⁻¹ * u.val) • a = a := by
      rw [mul_smul, he', inv_smul_smul]
    have hmem : v.val⁻¹ * u.val ∈ m22HexadPointwiseKernel B :=
      (m22HexadPointwiseKernel B).mul_mem
        ((m22HexadPointwiseKernel B).inv_mem v.property) u.property
    have hone : v.val⁻¹ * u.val = 1 := by
      by_contra hne
      exact hnot ((kernel_fixed_iff hB hmem hne a).mp hfix)
    exact Subtype.ext (inv_mul_eq_one.mp hone).symm
  have hn := Nat.card_le_card_of_injective f hi
  rw [m22HexadPointwiseKernel_card hB] at hn
  have hS : Nat.card S = S.card := by simp
  omega

/-- The hexad is the unique invariant six-point set of its pointwise kernel. -/
theorem invariant_six_eq_hexad {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (S : Finset (Fin 22)) (hc : S.card = 6)
    (hs : m22HexadPointwiseKernel B ≤ stabilizer M22 S) : S = B := by
  apply Finset.eq_of_subset_of_card_le (small_invariant_subset_hexad hB S (by omega) hs)
  rw [m22Block_card B hB, hc]

/-- The full design normalizer preserves the uniquely determined hexad. -/
theorem normalizer_le_hexad_stabilizer {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (X : Subgroup M22) (hX : X ≤ stabilizer M22 B)
    (hK : m22HexadPointwiseKernel B ≤ X) :
    normalizer (X.map M22ValueBound.Concrete.inclusion : Set m22DesignAut) ≤
      stabilizer m22DesignAut B := by
  intro g hg
  apply mem_stabilizer_iff.mpr
  apply invariant_six_eq_hexad hB (g • B) (by
    rw [Finset.card_smul_finset, m22Block_card B hB])
  intro u hu
  have hm : M22ValueBound.Concrete.inclusion u ∈ X.map M22ValueBound.Concrete.inclusion :=
    mem_map_of_mem _ (hK hu)
  have hn := (mem_normalizer_iff.mp
    ((normalizer (X.map M22ValueBound.Concrete.inclusion : Set m22DesignAut)).inv_mem hg)
      (M22ValueBound.Concrete.inclusion u)).mp hm
  obtain ⟨v, hv, he⟩ := hn
  have hvs : (M22ValueBound.Concrete.inclusion v : m22DesignAut) • B = B := hX hv
  have hmul : M22ValueBound.Concrete.inclusion u * g =
      g * M22ValueBound.Concrete.inclusion v := by
    rw [he]
    simp only [inv_inv, mul_inv_cancel_left, mul_assoc]
  change u • (g • B) = g • B
  change (M22ValueBound.Concrete.inclusion u : m22DesignAut) • (g • B) = g • B
  rw [← mul_smul, hmul, mul_smul, hvs]

/-- An ambient Sylow subgroup lying in a hexad stabilizer contains its pointwise kernel. -/
theorem kernel_le_of_sylow {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (U : Sylow 2 M22) (hU : (U : Subgroup M22) ≤ stabilizer M22 B) :
    m22HexadPointwiseKernel B ≤ U := by
  have h := (IsPGroup.of_card (n := 4) (m22HexadKernel_card hB)).le_sylow_of_normal
    (U.subtype hU)
  rintro u ⟨v, hv, rfl⟩
  exact h hv


end Sporadic.Mathieu.M22SolvableSylow
