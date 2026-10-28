module
public import Theory.GroupTheory.CComponent.Basic

/-!
# Equal images place a containing C-component in an overgroup

Let B be a C-component of H and let D be a C-component of M containing B.
If a homomorphism from M has kernel inside H and gives B and D the same
image, then D lies in H. Restriction makes B and D comparable C-components
of H, so they coincide. No quasisimplicity of either image is needed.

This is the quotient comparison used for the selected diagram component
in Aschbacher--Smith 14.2.9, printed p.983.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G X : Type*} [Group G] [Group X]

theorem cComponent_eq_of_equal_images_of_kernel_le
    (M H B D : Subgroup G) (f : M →* X)
    (hHM : H ≤ M) (hBH : B ≤ H) (hDM : D ≤ M) (hBD : B ≤ D)
    (hB : (B.subgroupOf H).IsCComponent)
    (hD : (D.subgroupOf M).IsCComponent)
    (hker : f.ker.map M.subtype ≤ H)
    (himage : (B.subgroupOf M).map f = (D.subgroupOf M).map f) : B = D := by
  have hDH : D ≤ H := by
    intro x hx
    let d : M := ⟨x, hDM hx⟩
    have hd : f d ∈ (B.subgroupOf M).map f :=
      himage.symm ▸ mem_map_of_mem f (show d ∈ D.subgroupOf M from hx)
    obtain ⟨b, hb, he⟩ := hd
    have hz : b⁻¹ * d ∈ f.ker := by
      change f (b⁻¹ * d) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    have hzH : ((b⁻¹ * d : M) : G) ∈ H :=
      hker (mem_map_of_mem M.subtype hz)
    have hh := H.mul_mem (hBH hb) hzH
    change (b : G) * ((b : G)⁻¹ * x) ∈ H at hh
    simpa only [mul_inv_cancel_left] using hh
  have he := hB.eq_of_le (hD.subgroupOf_of_le hDH hHM) (comap_mono hBD)
  simpa only [map_subgroupOf_eq_of_le hBH, map_subgroupOf_eq_of_le hDH]
    using congrArg (Subgroup.map H.subtype) he
end Theory.GroupTheory
