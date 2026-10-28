module

public import Theory.AlgebraicGroup.Parabolic.InvariantLeviGeometry.LeviStructure
public import Theory.AlgebraicGroup.Parabolic.InvariantLeviGeometry.FiniteApplication

/-!
# Finite projection with standard Levi separation discharged

The cocharacter separation theorem supplies disjointness for the literal
standard factors used by the finite projection. Its kernel and its identity
on the restricted Levi are the same as in the original consumer; no algebraic
or finite Levi reductivity premise is needed for this projection.

Source: GLS3, 1.13.3(a) and 2.6.5(e,g).
-/

namespace Theory.AlgebraicGroup.InvariantLeviGeometry

open FiniteParabolicRealization
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {K : Variety k} [AlgebraicGroup K]
  (S : StandardParabolicRelativeRootSetup K)
  (sigma : AlgebraicEndomorphism K) (p : ℕ) [Fact p.Prime] [CharP k p]

local notation "hD" => S.standardParabolic.left.right.left
local notation "hT" => S.standardParabolic.left.left.left
local notation "P" => parabolic S.D hD hT S.positiveRoots S.sigmaJ
local notation "U" => unipotent S.D hD S.positiveRoots S.sigmaJ
local notation "L" => levi S.D hD hT S.sigmaJ

/-- Apply the finite projection to the constructed standard factors, with the
source disjointness premise proved by cocharacter separation. -/
public theorem exists_finiteProjection_of_standard_setup
    (hpositive : S.positiveRoots = S.D.positive)
    (hsigmaU : (U).toSubgroup.map sigma.onPoints = (U).toSubgroup)
    (hsigmaL : (L).toSubgroup.map sigma.onPoints = (L).toSubgroup) :
    ∃ f : restrict sigma p (P).toSubgroup →* restrict sigma p (L).toSubgroup,
      Function.Surjective f ∧
      f.ker = (restrict sigma p (U).toSubgroup).subgroupOf
        (restrict sigma p (P).toSubgroup) ∧
      ∀ l : restrict sigma p (L).toSubgroup,
        f ⟨l, restrict_mono sigma p
          (factors_le S.D hD hT S.positiveRoots S.sigmaJ).2 l.property⟩ = l :=
  exists_finiteProjection S sigma p hpositive (unipotent_disjoint_levi S) hsigmaU hsigmaL

end Theory.AlgebraicGroup.InvariantLeviGeometry
