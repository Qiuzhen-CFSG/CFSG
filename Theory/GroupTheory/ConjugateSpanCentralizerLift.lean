module
public import Theory.GroupTheory.ConjugateSpanOrder
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Conjugate generation through a centralizing kernel

If C ≤ L covers L/N and N fixes a seed Z pointwise, the L-conjugates
of Z are already its C-conjugates. For each l choose c with the same
quotient image; the remaining factor c⁻¹l fixes Z. The quotient map and
both ambient subgroup inclusions are retained.

This is the centralizer-covering step for the original omega-generated
module in Aschbacher–Smith 5.2.2, printed p.648.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- A quotient-covering subgroup generates the same conjugate span when the kernel fixes the seed. -/
theorem conjugateSpanBy_eq_of_quotient_surjective
    (Z L C : Subgroup G) (N : Subgroup L) [N.Normal] (hCL : C ≤ L)
    (hs : Function.Surjective ((QuotientGroup.mk' N).comp (inclusion hCL)))
    (hc : N.map L.subtype ≤ centralizer (Z : Set G)) :
    conjugateSpanBy Z L = conjugateSpanBy Z C := by
  apply le_antisymm ?_ (conjugateSpanBy_mono le_rfl hCL)
  apply (closure_le _).mpr
  rintro x ⟨l,hl,z,hz,rfl⟩
  obtain ⟨c,he⟩ := hs (QuotientGroup.mk' N ⟨l,hl⟩)
  have hk : (inclusion hCL c)⁻¹ * (⟨l,hl⟩ : L) ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N ((inclusion hCL c)⁻¹ * (⟨l,hl⟩ : L)) = 1
    rw [map_mul,map_inv]
    change ((QuotientGroup.mk' N).comp (inclusion hCL) c)⁻¹ *
      QuotientGroup.mk' N ⟨l,hl⟩ = 1
    rw [he,inv_mul_cancel]
  have hcz : ((c : G)⁻¹ * l) * z * ((c : G)⁻¹ * l)⁻¹ = z :=
    mul_inv_eq_iff_eq_mul.mpr ((hc (mem_map_of_mem L.subtype hk) z hz).symm)
  have hconj : l * z * l⁻¹ = (c : G) * z * (c : G)⁻¹ := by
    calc
      _ = (c : G) * (((c : G)⁻¹ * l) * z * ((c : G)⁻¹ * l)⁻¹) * (c : G)⁻¹ := by group
      _ = _ := by rw [hcz]
  rw [hconj]
  exact subset_closure ⟨c,c.property,z,hz,rfl⟩
end Subgroup
