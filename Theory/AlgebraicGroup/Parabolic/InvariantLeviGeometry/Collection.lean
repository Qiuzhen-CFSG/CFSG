module

public import Theory.AlgebraicGroup.Parabolic.InvariantLeviGeometry
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicNormalizer
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicLeviAction
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.StandardUnipotentRootProduct

/-!
# Collection in a standard parabolic

The relative-height commutator estimates show that the full Levi factor and
all parabolic roots normalize the positive roots outside the Levi subsystem.
The generated-group decomposition is therefore a pointwise `U L` product,
with normality relative to `P`. Finite-height collection also proves that `U`
is unipotent. No disjointness, reductivity or radical maximality is assumed.

The input `StandardParabolicRelativeRootSetup` contains compatible actual root
data and Chevalley relations. Its closed subgroup `U` is specified only by
root generation; it is not assumed to be a radical. Our closed construction
identifies that subgroup with the exact candidate used here.

Source: GLS3, Theorem 1.13.3(a,b), collection portion of the proof.
-/

namespace Theory.AlgebraicGroup.InvariantLeviGeometry

open scoped Pointwise
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {K : Variety k} [AlgebraicGroup K]
  (S : StandardParabolicRelativeRootSetup K)

local notation "hD" => S.standardParabolic.left.right.left
local notation "hT" => S.standardParabolic.left.left.left
local notation "P" => parabolic S.D hD hT S.positiveRoots S.sigmaJ
local notation "U" => unipotent S.D hD S.positiveRoots S.sigmaJ
local notation "L" => levi S.D hD hT S.sigmaJ

/-- The relative-root setup's specified root group is the constructed closed
candidate, without using any radical identification. -/
public theorem unipotent_eq_setup : U = S.U := by
  apply SetLike.coe_injective
  change (standardUnipotentRootFactor S.D S.positiveRoots S.sigmaJ :
    Set (Variety.Point K)) = (S.U.toSubgroup : Set (Variety.Point K))
  rw [S.unipotentRootGeneration]
  rfl

/-- Chevalley collection puts the standard Levi in the normalizer of `U`. -/
public theorem levi_le_unipotent_normalizer :
    (L).toSubgroup ≤ Subgroup.normalizer ((U).toSubgroup : Set (Variety.Point K)) := by
  rw [unipotent_toSubgroup, standardUnipotentRootFactor_eq_firstRelativeRootLayer S,
    levi_toSubgroup]
  exact standardLeviSubgroup_le_relativeRootLayer_normalizer S 1

/-- The standard unipotent subgroup is normal inside the constructed parabolic. -/
public theorem unipotent_normal : ((U).toSubgroup.subgroupOf (P).toSubgroup).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (factors_le S.D hD hT S.positiveRoots S.sigmaJ).1).mpr
  rw [← factors_sup S.D hD hT S.positiveRoots S.sigmaJ]
  exact sup_le (U).toSubgroup.le_normalizer (levi_le_unipotent_normalizer S)

/-- The Levi and unipotent factors multiply in the literal order used by the
finite Levi projection consumer. -/
public theorem mem_parabolic_iff (x : Variety.Point K) :
    x ∈ P ↔ ∃ u ∈ U, ∃ l ∈ L, x = u * l := by
  have hproduct : ((P).toSubgroup : Set (Variety.Point K)) =
      ((U).toSubgroup : Set (Variety.Point K)) * ((L).toSubgroup : Set (Variety.Point K)) := by
    rw [← factors_sup S.D hD hT S.positiveRoots S.sigmaJ]
    exact Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (levi_le_unipotent_normalizer S)
  change x ∈ ((P).toSubgroup : Set (Variety.Point K)) ↔ _
  rw [hproduct]
  constructor
  · rintro ⟨u, hu, l, hl, heq⟩
    exact ⟨u, hu, l, hl, heq.symm⟩
  · rintro ⟨u, hu, l, hl, rfl⟩
    exact Set.mul_mem_mul hu hl

/-- The closure used in the existing candidate adds no points to our exact
root-generated construction. -/
public theorem unipotent_eq_candidate :
    U = unipotentCandidate S.T S.D S.positiveRoots S.J := by
  rw [unipotentCandidate_spec]
  apply SetLike.coe_injective
  change (standardUnipotentRootFactor S.D S.positiveRoots S.sigmaJ :
      Set (Variety.Point K)) =
    closure (standardUnipotentRootFactor S.D S.positiveRoots
      (RootSubsystemSpan S.D S.J) : Set (Variety.Point K))
  rw [← S.standardParabolic.2.2]
  exact (Variety.isClosed_iff_isZariskiClosed.mpr
    (S.D.generated_isZariskiClosed hD (S.positiveRoots \ S.sigmaJ))).closure_eq.symm

/-- Nilpotent relative-height collection proves unipotence of the constructed
factor; maximality as the radical is a separate source obligation. -/
public theorem unipotent_isUnipotent (hpositive : S.positiveRoots = S.D.positive) :
    IsUnipotentAlgebraicGroup (U).carrierVariety := by
  classical
  let := Fintype.ofFinite S.D.Root
  let := Fintype.ofFinite S.ι
  rw [unipotent_eq_candidate S]
  exact unipotentCandidate_isUnipotentAlgebraicGroup S.T S.B S.D
    S.integralPairing S.integralBase S.rootEquiv S.weightEquiv
    S.rationalPairing S.rationalBase S.baseSupport_eq S.C S.coeff
    S.positiveRoots (hpositive ▸ S.actualRootDatum)
    S.integralSimpleRootExpansion S.rationalSimpleRootExpansion S.chevalleySystem
    S.standardParabolic.1 hpositive S.J S.standardParabolic.2.1

end Theory.AlgebraicGroup.InvariantLeviGeometry
