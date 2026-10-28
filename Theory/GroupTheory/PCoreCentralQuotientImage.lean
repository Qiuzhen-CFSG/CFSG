module

public import Theory.GroupTheory.PCoreCentralQuotient
public import Theory.GroupTheory.PCoreSurjective

/-!
# The literal core image in a central quotient

If the p-core is self-centralizing, every central subgroup lies in it.
Consequently the image of the core in a central quotient is the quotient's
p-core, and is self-centralizing there. This combines characteristic-p
descent with p-core lifting through a p-group kernel.

Source application: Aschbacher--Smith, Lemma 14.2.21, chain (*), printed
p.988. The denominator is the given central subgroup, and the numerator
is the image under its actual quotient map.
-/

namespace Subgroup

/-- The actual image of a self-centralizing p-core is self-centralizing after
quotienting by any central subgroup. -/
public theorem centralizer_image_pCore_le_of_central_quotient
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ center G)
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G) :
    centralizer ((pCore p G).map (QuotientGroup.mk' Z) : Set (G ⧸ Z)) ≤
      (pCore p G).map (QuotientGroup.mk' Z) := by
  have hZQ : Z ≤ pCore p G := (hZ.trans (center_le_centralizer _)).trans hc
  have he : (pCore p G).map (QuotientGroup.mk' Z) = pCore p (G ⧸ Z) := by
    rw [← (QuotientGroup.mk' Z).comap_pCore_of_ker_isPGroup
      (QuotientGroup.mk'_surjective Z) (by
        rw [QuotientGroup.ker_mk']
        exact pCore_isPGroup.to_le hZQ), map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective Z)]
  rw [he]
  exact (QuotientGroup.mk' Z).centralizer_pCore_le_of_surjective_centralKernel
    (QuotientGroup.mk'_surjective Z) (by rwa [QuotientGroup.ker_mk']) hc

end Subgroup
