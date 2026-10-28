module
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.GroupTheory.PGroup

/-!
# A central cubic on the natural SL₃(4)-module

The center has order three. Its nonidentity scalar acts without nonzero
fixed vectors, including after restriction of scalars to the binary field.
This is the natural-module movement used in the linear-three branch of
Aschbacher–Smith 10.2.9 (printed pp.751–752).
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Theory.SpecificGroups.PSL3.FourScalar
variable {F : Type*} [Field F] [Finite F]

theorem exists_central_cubic_moving (hF : Nat.card F = 4) :
    ∃ x : SL(3,F), orderOf x = 3 ∧ x ∈ center SL(3,F) ∧
      ∀ v : Fin 3 → F, x.val.mulVec v = v → v = 0 := by
  have hc : Nat.card (center SL(3,F)) = 3 := by
    rw [Atlas.ExceptionalSupport.card_sl_center,hF]
    norm_num
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := center SL(3,F)) 3
    (by rw [hc])
  refine ⟨x,(Subgroup.orderOf_coe x).trans hx,x.property,?_⟩
  obtain ⟨s,hs,he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp x.property
  have hsne : s ≠ 1 := by
    intro h
    have hx1 : (x : SL(3,F)) = 1 := by
      apply Subtype.ext
      rw [←he,h]
      simp
    have hh : orderOf (x : SL(3,F)) = 3 := (Subgroup.orderOf_coe x).trans hx
    rw [hx1,orderOf_one] at hh
    omega
  intro v hv
  have hh : (s-1) • v = 0 := by
    rw [sub_smul,one_smul,sub_eq_zero]
    rw [←he] at hv
    change (diagonal (fun _ : Fin 3 => s)) *ᵥ v = v at hv
    rwa [Matrix.diagonal_const_mulVec] at hv
  exact (smul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hsne)
end Theory.SpecificGroups.PSL3.FourScalar
