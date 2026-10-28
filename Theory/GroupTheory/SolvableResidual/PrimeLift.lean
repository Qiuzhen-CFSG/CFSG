module

public import Theory.GroupTheory.SolvableResidual
public import Mathlib.GroupTheory.Index

/-!
# Lifting residual membership across a coprime kernel

If an element has residual image, its image modulo the domain's solvable
residual is represented by a kernel element. The order of that image divides
both the original element order and the kernel order. Coprimality therefore
puts the original element in the residual.

This is used for the marked cubic in the simultaneous centralizer of the
full J₄ cover in Aschbacher--Smith 4.2.13, printed p.612.
-/

public noncomputable section
open Subgroup

namespace Subgroup
/-- An element of kernel-coprime order lies in the residual if its image does. -/
theorem mem_solvableResidual_of_image_of_coprime_order {U Y : Type*} [Group U] [Finite U]
    [Group Y] (f : U →* Y) (hf : Function.Surjective f)
    {p : ℕ} (hc : Nat.Coprime p (Nat.card f.ker))
    (x : U) (hx : orderOf x = p) (hy : f x ∈ solvableResidual Y) :
    x ∈ solvableResidual U := by
  have hm := map_solvableResidual_eq f hf
  obtain ⟨s,hs,hsx⟩ := hm.symm ▸ hy
  let q := QuotientGroup.mk' (solvableResidual U)
  have hsk : x * s⁻¹ ∈ f.ker := by
    change f (x * s⁻¹) = 1
    rw [map_mul,map_inv,hsx,mul_inv_cancel]
  have hqs : q s = 1 := (QuotientGroup.eq_one_iff s).mpr hs
  have hz : q x ∈ f.ker.map q := by
    refine ⟨x * s⁻¹,hsk,?_⟩
    rw [map_mul,map_inv,hqs,inv_one,mul_one]
  let z : f.ker.map q := ⟨q x,hz⟩
  have hp : orderOf z ∣ p := by
    rw [←orderOf_coe z]
    exact hx ▸ orderOf_map_dvd q x
  have hc' := hc.of_dvd_right (card_map_dvd f.ker q)
  have he : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hc' hp (_root_.orderOf_dvd_natCard z)
  exact (QuotientGroup.eq_one_iff x).mp
    (congrArg (fun y : f.ker.map q => (y : U ⧸ solvableResidual U))
      (orderOf_eq_one_iff.mp he))
end Subgroup
