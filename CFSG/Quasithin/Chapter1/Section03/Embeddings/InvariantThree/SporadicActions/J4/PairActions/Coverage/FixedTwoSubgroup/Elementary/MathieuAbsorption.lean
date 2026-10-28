module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.MathieuAbsorption.Quotient

/-!
# Assembly of elementary-pair absorption from max1

The quotient reduction preserves the original elementary-nine subgroup,
Sylow subgroup and their setwise permutability. It identifies their product
with a full Mathieu inverse image. A proved placement of those inverse
images would therefore place both original subgroups in the same actual
conjugate of max4.

The incidence premise remains unproved. The conditional theorem below does
not establish `elementaryMathieuAbsorption` or the source proposition.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), citing Aschbacher (1986).
-/

public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

open MathieuAbsorption

/-- Conditional assembly; the fixed-Sylow inverse-image containment must still be proved. -/
theorem elementaryMathieuAbsorption_of_fixedSylowPreimagePlacement
    (hfixed : FixedSylowPreimagePlacement) : ElementaryMathieuAbsorption := by
  intro _ _ _ S R h hE hcard hS hR
  obtain ⟨g, hg⟩ := preimagePlacement_of_fixed hfixed h.stronglyQuasithin h.rank
    (sylowImage S hS) (image R)
    (image_elementary hR hE) ((image_card hR hE).trans hcard) (image_permutes h hS hR)
  rw [sylowImage_coe, preimage_join S hS hR] at hg
  exact ⟨g, le_sup_right.trans hg, le_sup_left.trans hg⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
