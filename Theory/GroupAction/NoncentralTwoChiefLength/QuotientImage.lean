module
public import Theory.GroupAction.NoncentralTwoChiefLength.SectionMaps
/-!
# Cubic length on an ambient quotient image

Coprime fixed-point lifting equates the contribution of a normal two-group
section with the conjugation length of its literal image in the ambient
quotient. The actor is mapped by the same quotient homomorphism.
This transports the chief-series bound on V_H/U_H to the original subgroup
filtration in Aschbacher--Smith 13.8.33, printed p.967.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Coprime fixed-point lifting identifies a section contribution with the
literal image in the ambient quotient, keeping the quotient actor. -/
theorem sectionCubicLength_eq_quotient_image (A R N : Subgroup G) [N.Normal]
    (hA : IsPGroup 3 A) (hR : IsPGroup 2 R) (hNR : N ≤ R)
    (hAR : A ≤ normalizer (R : Set G)) :
    sectionCubicLength A N R = conjugationCubicLength
      (A.map (QuotientGroup.mk' N)) (R.map (QuotientGroup.mk' N)) := by
  let π := QuotientGroup.mk' N
  have hn : A.map π ≤ normalizer (R.map π : Set (G ⧸ N)) :=
    (map_mono hAR).trans (le_normalizer_map π)
  let := conjMulDistribMulActionOfLeNormalizer (A.map π) (R.map π) hn
  let f : A →* A.map π := π.subgroupMap A
  let s : ConjugationSection (Y := R.map π) A N R f := {
    le := hNR
    normalizes := hAR
    projection := π.subgroupMap R
    onto := by rintro ⟨_,x,hx,rfl⟩; exact ⟨⟨x,hx⟩,rfl⟩
    kernel := by
      ext x
      change (π.subgroupMap R) x = 1 ↔ (x : G) ∈ N
      rw [← Subtype.coe_inj]
      exact QuotientGroup.eq_one_iff (x : G)
    equivariant := by
      intro a r
      apply Subtype.ext
      change π ((a : G) * (r : G) * (a : G)⁻¹) = _
      simp only [map_mul,map_inv]
      rfl }
  have hf : Function.Surjective f := by
    rintro ⟨_,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  exact (s.length_eq hA hR hf).trans (conjugationCubicLength_eq _ _ hn).symm
end Subgroup
