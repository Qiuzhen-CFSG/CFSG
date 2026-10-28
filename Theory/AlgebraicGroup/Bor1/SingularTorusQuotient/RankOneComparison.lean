module
public import Theory.AlgebraicGroup.Tori.MaximalDimension
public import Theory.AlgebraicGroup.Bor1.GeometricCertificates
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry

/-!
# Matching the rank-one source geometry to the actual quotient

The radical-quotient certificate stores one maximal torus of dimension one.
Every maximal torus of that same quotient has dimension one by proved Borel
and connected-solvable torus conjugacy. A maximal torus contained in any given
quotient Borel is constructed using Borel conjugacy.

These comparisons allow the two exact source results used in 13.15 to retain
their primary hypotheses: a Borel containing a specified dimension-one
maximal torus, and two distinct Borels containing the same such torus. The
maps and algebraic-group instance of the original radical quotient are kept.
Source: Borel, *Linear Algebraic Groups*, IV, 13.11--13.15.
-/

public section
namespace Theory.AlgebraicGroup.Bor1.SingularTorusQuotient
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- The actual quotient torus may be replaced by any other maximal torus,
in particular the image of the original ambient torus. -/
theorem rankOne_quotient_maximalTorus_dimension {C : ClosedSubgroup G}
    (c : SemisimpleRankOneQuotientCertificate C) :
    letI : AlgebraicGroup c.quotient := c.quotientAlgebraicGroup
    ∀ D : ClosedSubgroup c.quotient, IsMaximalTorus D →
      Variety.dimension D.carrierVariety = 1 := by
  let _ : AlgebraicGroup c.quotient := c.quotientAlgebraicGroup
  intro D hD
  exact (maximalTorus_dimension_eq hD c.quotientTorus_isMaximal).trans
    c.quotientTorus_dimension

/-- The primary rank-one theorem for a Borel containing the marked torus
suffices for every actual quotient Borel. Its containing maximal torus is
constructed, not supplied as an additional source assumption. -/
theorem rankOne_quotient_borel_radical_dimension_le {C : ClosedSubgroup G}
    (c : SemisimpleRankOneQuotientCertificate C) :
    letI : AlgebraicGroup c.quotient := c.quotientAlgebraicGroup
    (∀ D A N : ClosedSubgroup c.quotient, IsMaximalTorus D →
      Variety.dimension D.carrierVariety = 1 → IsBorelSubgroup A → D ≤ A →
      IsUnipotentRadicalOf A N → Variety.dimension N.carrierVariety ≤ 1) →
    ∀ A N : ClosedSubgroup c.quotient, IsBorelSubgroup A →
      IsUnipotentRadicalOf A N → Variety.dimension N.carrierVariety ≤ 1 := by
  let _ : AlgebraicGroup c.quotient := c.quotientAlgebraicGroup
  intro hsmall A N hA hN
  obtain ⟨D,hD,hDA⟩ := BorelIntersectionGeometry.exists_maximalTorus_le_borel_of_conjugacy
    (fun _ _ hB hB' => BorelGeometricConjugacy.conjugacy hB hB') A hA
  exact hsmall D A N hD (rankOne_quotient_maximalTorus_dimension c D hD) hA hDA hN

/-- Rank-one intersection geometry applies to the actual common maximal
torus of the two restricted quotient Borels, without identifying it with
the certificate's chosen torus. -/
theorem rankOne_quotient_borel_intersection_isSubtorus {C : ClosedSubgroup G}
    (c : SemisimpleRankOneQuotientCertificate C) :
    letI : AlgebraicGroup c.quotient := c.quotientAlgebraicGroup
    (∀ D A A' : ClosedSubgroup c.quotient, IsMaximalTorus D →
      Variety.dimension D.carrierVariety = 1 → IsBorelSubgroup A →
      IsBorelSubgroup A' → D ≤ A → D ≤ A' → A ≠ A' → IsSubtorus (A.inter A')) →
    ∀ A A' D : ClosedSubgroup c.quotient, IsBorelSubgroup A → IsBorelSubgroup A' →
      IsMaximalTorus D → D ≤ A → D ≤ A' → A ≠ A' → IsSubtorus (A.inter A') := by
  let _ : AlgebraicGroup c.quotient := c.quotientAlgebraicGroup
  intro hgeometry A A' D hA hA' hD hDA hDA' hne
  exact hgeometry D A A' hD (rankOne_quotient_maximalTorus_dimension c D hD)
    hA hA' hDA hDA' hne

end Theory.AlgebraicGroup.Bor1.SingularTorusQuotient
