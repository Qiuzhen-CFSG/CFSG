module

public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# Recovering a subnormal p-perfect subgroup from its core-quotient image

For a subnormal p-perfect subgroup J, the full preimage of its image
modulo the ambient p-core is J O_p(G). The p-core supplies a p-group
supplement, so the subnormal supplement theorem identifies the p-residual
of this literal preimage with J. This preserves the original quotient map.

Source: Aschbacher--Smith A.4.2(2), used in13.7.4(1), pp.57,936.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G] {p : ℕ}

/-- A subnormal p-perfect subgroup is the residual of the full preimage
of its actual image in G/O_p(G). -/
theorem residual_core_preimage_eq (J : Subgroup G)
    (hn : J.IsSubnormal) (hp : IsPPerfect p J) :
    (pResidual p ((J.map (QuotientGroup.mk' (pCore p G))).comap
      (QuotientGroup.mk' (pCore p G)))).map
        ((J.map (QuotientGroup.mk' (pCore p G))).comap
          (QuotientGroup.mk' (pCore p G))).subtype = J := by
  rw [comap_map_eq, QuotientGroup.ker_mk']
  let S := J ⊔ pCore p G
  have hJS : J ≤ S := le_sup_left
  have hQS : pCore p G ≤ S := le_sup_right
  have hprod : ∀ g : S, ∃ j ∈ J.subgroupOf S,
      ∃ q ∈ (pCore p G).subgroupOf S, j * q = g := by
    intro g
    have hg : (g : G) ∈ (J : Set G) * (pCore p G : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right J (pCore p G)
        (by rw [normalizer_eq_top]; exact le_top)]
      exact g.property
    obtain ⟨j, hj, q, hq, he⟩ := hg
    exact ⟨⟨j, hJS hj⟩, hj, ⟨q, hQS hq⟩, hq, Subtype.ext he⟩
  have he := pResidual_eq_of_subnormal_product (J.subgroupOf S)
    ((pCore p G).subgroupOf S) hn.subgroupOf
    (hp.of_surjective (subgroupOfEquivOfLe hJS).symm.toMonoidHom
      (subgroupOfEquivOfLe hJS).symm.surjective)
    pCore_isPGroup.comap_subtype hprod
  rw [he, map_subgroupOf_eq_of_le hJS]

end Theory.GroupTheory
