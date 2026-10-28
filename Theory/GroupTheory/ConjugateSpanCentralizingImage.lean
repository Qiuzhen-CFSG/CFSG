module
public import Theory.GroupTheory.AbelianConjugateSpan

/-!
# Centralizing a conjugate span through a quotient

If R and the kernel of a homomorphism fix Z, and the images of R and K
commute, then R fixes the K-conjugate span of Z. The preimage of the
image of R is R times the kernel; K normalizes this subgroup. Relative
normality therefore propagates fixation from the seed to its whole span.

This elementary lemma supplies the Thompson-action comparison in
Aschbacher--Smith 13.2.12, printed p.882.
-/

public section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Group D]

theorem centralizes_span_of_centralizing_images
    (f : G →* D) (R K Z : Subgroup G)
    (hR : R ≤ centralizer (Z : Set G))
    (hk : f.ker ≤ centralizer (Z : Set G))
    (hc : R.map f ≤ centralizer (K.map f : Set D)) :
    R ≤ centralizer (conjugateSpanBy Z K : Set G) := by
  let C := (R.map f).comap f
  have hRC : R ≤ C := le_comap_map f R
  have hC : C ≤ centralizer (Z : Set G) := by
    change (R.map f).comap f ≤ _
    rw [comap_map_eq]
    exact sup_le hR hk
  have hn : K ≤ normalizer (C : Set G) := by
    apply le_normalizer_iff.mpr
    intro k hk y hy
    change f (k*y*k⁻¹) ∈ R.map f
    have he := mem_centralizer_iff.mp (hc hy) (f k) (mem_map_of_mem f hk)
    rw [map_mul,map_mul,map_inv,he,mul_inv_cancel_right]
    exact hy
  exact hRC.trans (le_centralizer_conjugateSpanBy_of_normalizes C Z K hn hC)
end Subgroup
