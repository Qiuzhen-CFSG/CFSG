module

public import CFSG.Quasithin.ChapterE.Section01.ReverseLift.Preparation
public import CFSG.Quasithin.ChapterE.Section01.ReverseLift.Odd
public import CFSG.Quasithin.ChapterE.Section01.ReverseLift.Component

/-!
# Reverse quotient lifting of E-members

Every rank-bounded E-member in `G/Y` has an E-member upstairs with the same
bound whose two-residual maps onto its intrinsic two-residual. We split on
the two alternatives of E.1.2. The odd branch shrinks to the residual--tau
subgroup and uses a minimal supplement; the component branch lifts through
the canonical radical-quotient isomorphism of a minimal supplement. Both
branches use the source section `O²(G)Y` in the appropriate preimage group.
Their local membership conclusions inherit to the original ambient group
by E.1.8(2). No choice of supplement or membership certificate is assumed.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.10(7), printed pp.211--212.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- E.1.10(7): a quotient E-member lifts with its rank bound and its exact
embedded two-residual. The image of the lifted member itself may be smaller
than the original quotient member. -/
theorem IsEMemberAt.exists_quotient_lift {i : ℕ} (T : Sylow 2 G)
    (A Y : Subgroup G) [Y.Normal] [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) {I : Subgroup (G ⧸ Y)}
    (hI : IsEMemberAt i ((T : Subgroup G).map (QuotientGroup.mk' Y))
      (A.map (QuotientGroup.mk' Y)) I) :
    ∃ J : Subgroup G, IsEMemberAt i (T : Subgroup G) A J ∧
      ((pResidual 2 J).map J.subtype).map (QuotientGroup.mk' Y) =
        (pResidual 2 I).map I.subtype := by
  rcases hI.2 with ⟨ho, hi⟩ | ⟨hc, hi⟩
  · exact exists_odd_quotient_lift T A Y hAT hI.1 ho hi
  · exact exists_component_quotient_lift T A Y hAT hI.1 hc hi

end CFSG.Quasithin.ChapterE
