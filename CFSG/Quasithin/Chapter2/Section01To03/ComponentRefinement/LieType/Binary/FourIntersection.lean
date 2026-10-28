module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.FourIntersection.Reduction
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.FourIntersection.OvergroupCover
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.FourIntersection.DiagramExchange

/-!
# The degree-four binary intersection

The intrinsic intersection M ∩ L is a proper overgroup of the transvection
centralizer, so it lies in the image-line or fixed-hyperplane stabilizer.
The actual nontrivial diagram action exchanges these two parabolics. Since
N_S(L) preserves M ∩ L, the intersection lies in both, and hence equals the
centralizer. The two geometric inputs of the reduction are discharged by
the proved overgroup cover and parabolic exchange.

This establishes the intersection clause of Aschbacher–Smith 2.3.9(7)(g),
combined manuscript of 1 March 2004, printed pp.525–526
(`refs/quasithin.pdf`), under the explicit rank-one-coordinate and nontrivial
diagram-action hypotheses. Their construction from the source setup remains
with the parent binary refinement.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.FourIntersection

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The degree-four intersection equals the centralizer of the involution
projection when its rank-one coordinates and actual nontrivial diagram action
are supplied. No overgroup-cover or parabolic-exchange premise remains. -/
theorem intersection_eq_centralizer (h : LocalSetup H L M S z)
    (e : L ≃* PSL 4) {t : L} (ht : IsConjugationProjection L z t)
    (_ht2 : orderOf t = 2) (c : TransvectionCoordinates e t)
    (hd : NontrivialDynkinAction e ((S : Subgroup H).map H.subtype)) :
    L ⊓ M = L ⊓ Subgroup.centralizer ({(t : G)} : Set G) :=
  intersection_eq_of_geometric_inputs h e ht c hd
    (proper_overgroup_cover e c)
    (parabolics_exchanged_of_dimension_change e c (proper_overgroup_cover e c))

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.FourIntersection

end
