module
public import Theory.GroupTheory.NormalCentralQuotientAction
import all Theory.GroupTheory.NormalCentralQuotientAction

/-!
# The canonical central quotient on representatives

The third-isomorphism equivalence from G/centralPreimage(N) to
(G/N)/Z(G/N) sends the class of g to its successive quotient classes.
This specification lets conjugation consumers compare the two quotient
conventions without unfolding the equivalence.

The private import deliberately couples this proof extension to the defining
module's implementation; the existing definition and its public boundary are
unchanged. Only the representative equation is re-exported as a new theorem.
The source application is Aschbacher–Smith 13.8.21(2), p.956, where N=O₂(K).
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
/-- The third-isomorphism equivalence commutes with the two quotient projections. -/
theorem centralPreimageQuotientEquiv_mk (g : G) :
    centralPreimageQuotientEquiv N (QuotientGroup.mk' (centralPreimage N) g) =
      QuotientGroup.mk' (center (G ⧸ N)) (QuotientGroup.mk' N g) := by
  unfold centralPreimageQuotientEquiv
  rfl
end Subgroup
