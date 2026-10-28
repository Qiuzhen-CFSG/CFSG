module

public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Confining a normalizer by realizing its automorphisms locally

If a subgroup M contains C_G(A) and its elements in N_G(A) realize every
automorphism of A, then M contains N_G(A). Match an ambient normalizer
element with a local element inducing the same automorphism; their quotient
lies in the centralizer. This elementary normalizer/centralizer argument
reduces the confinement assertion in Thompson VI, printed p.630.
-/

namespace Subgroup

/-- Local realization of all automorphisms reduces normalizer confinement
to centralizer confinement. -/
public theorem normalizer_le_of_centralizer_le_of_surjective
    {G : Type*} [Group G] (A M : Subgroup G)
    (hC : centralizer (A : Set G) ≤ M)
    (hAut : Function.Surjective (A.normalizerMonoidHom.comp
      (M.subgroupOf (normalizer (A : Set G))).subtype)) :
    normalizer (A : Set G) ≤ M := by
  intro g hg
  let n : normalizer (A : Set G) := ⟨g, hg⟩
  obtain ⟨m, hm⟩ := hAut (A.normalizerMonoidHom n)
  have hker : (m : normalizer (A : Set G))⁻¹ * n ∈ A.normalizerMonoidHom.ker := by
    change A.normalizerMonoidHom ((m : normalizer (A : Set G))⁻¹ * n) = 1
    change A.normalizerMonoidHom (m : normalizer (A : Set G)) =
      A.normalizerMonoidHom n at hm
    rw [map_mul, map_inv, hm, inv_mul_cancel]
  rw [normalizerMonoidHom_ker] at hker
  have hmem := M.mul_mem m.property (hC hker)
  change ((m : normalizer (A : Set G)) : G) *
    (((m : normalizer (A : Set G)) : G)⁻¹ * g) ∈ M at hmem
  simpa only [mul_inv_cancel_left] using hmem

end Subgroup
