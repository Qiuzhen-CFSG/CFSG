module

public import Theory.AlgebraicGroup.Bor1.BorelHomogeneousSpace
public import Theory.AlgebraicGroup.Borel.StandardPositiveSystemClassification.Defs

universe u v

/-!
The fixed-coset extraction underlying Bor1, Proposition 13.7.

The source obtains a second maximal-torus-fixed point on the quotient `K / P`,
then lifts it through `K / B → K / P` and chooses a fixed point in the complete
stable fibre.  The present affine variety layer already provides the Pluecker
point model of `K / B` and the fixed-point-to-conjugate-Borel bridge, but it has
no non-affine quotient or complete-fibre construction.  We therefore expose
that missing geometric input as a certificate and prove the complete algebraic
extraction from it: a fixed lift gives `T ≤ B.carrier.conjugate y`, while the
non-base quotient point gives `y ∉ P`.

The certificate is intentionally below the group-theoretic normalizer and
self-normalization tail of Proposition 13.7.  It does not use root-data
generation or the numbered GLS3 root-structure theorems.
-/

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

section

variable {K : Variety k} [AlgebraicGroup K]

/-- Pointwise fixedness for an explicitly supplied action. -/
public def pointwiseFixedByAction {Γ X : Type*} [Group Γ]
    (action : MulAction Γ X) (S : Subgroup Γ) (x : X) : Prop :=
  letI : MulAction Γ X := action
  ∀ s : Γ, s ∈ S → s • x = x

/-- The quotient and stable-fibre data used by the Bor1 13.5--13.6 route.

`quotientBaseFiber` identifies the base fibre with `P`; `secondFixedPoint`
records the projective fixed-point theorem on `K / P`; and `fixedFiberLift`
records the fixed point supplied by the complete stable fibre over a non-base
quotient point.  The latter two fields are the non-affine geometric boundary
and are to be constructed by the complete-action prerequisite.
-/
public structure Bor1Theorem13_7FixedCosetCertificate
    (T P : ClosedSubgroup K) where
  containsBorels : ∀ B : BorelContaining T, B.carrier ≤ P
  quotient : Type v
  quotientAction : MulAction (Variety.Point K) quotient
  quotientProjection : Variety.Point K → quotient
  quotientBasePoint : quotient
  quotientBaseFiber : ∀ y : Variety.Point K,
    quotientProjection y = quotientBasePoint ↔ y ∈ P.toSubgroup
  secondFixedPoint : P.toSubgroup ≠ ⊤ →
    ∃ q : quotient, q ≠ quotientBasePoint ∧
      pointwiseFixedByAction quotientAction T.toSubgroup q
  fixedFiberLift : ∀ q : quotient,
    q ≠ quotientBasePoint →
      pointwiseFixedByAction quotientAction T.toSubgroup q →
    ∃ (B : BorelContaining T) (x : borelHomogeneousSpace B.carrier)
      (y : Variety.Point K),
      x = borelHomogeneousSpace.projection B.carrier y ∧
        (∀ t : Variety.Point K, t ∈ T.toSubgroup → t • x = x) ∧
        quotientProjection y = q

/-- Extract the escaping fixed-Borel coset from the 13.5--13.6 certificate. -/
public theorem exists_fixedBorelCoset_of_bor1Theorem13_7Certificate
    (T P : ClosedSubgroup K)
    (C : Bor1Theorem13_7FixedCosetCertificate T P)
    (hP : P.toSubgroup ≠ ⊤) :
    ∃ (B : BorelContaining T) (y : Variety.Point K),
      y ∉ P.toSubgroup ∧ T ≤ B.carrier.conjugate y := by
  obtain ⟨q, hqne, hqfix⟩ := C.secondFixedPoint hP
  obtain ⟨B, x, y, hxy, hxfixed, hyq⟩ := C.fixedFiberLift q hqne hqfix
  have hfixy : ∀ t : Variety.Point K, t ∈ T.toSubgroup →
      letI : MulAction (Variety.Point K)
          (borelPluckerAmbient B.carrier) :=
        borelPluckerAction B.carrier
      t • (y • borelPluckerBasePoint B.carrier) =
        y • borelPluckerBasePoint B.carrier := by
    intro t ht
    have hx := hxfixed t ht
    have hx' := congrArg (fun z : borelHomogeneousSpace B.carrier =>
      (z : borelPluckerAmbient B.carrier)) hx
    change t • (x : borelPluckerAmbient B.carrier) =
      (x : borelPluckerAmbient B.carrier) at hx'
    rw [hxy, borelHomogeneousSpace.projection_coe] at hx'
    exact hx'
  have hconj : T.toSubgroup ≤ (B.carrier.conjugate y).toSubgroup := by
    exact subgroup_le_conjugate_of_borel_homogeneousSpace_fixed
      B.carrier T.toSubgroup y hfixy
  have hynot : y ∉ P.toSubgroup := by
    intro hyp
    have hbase : C.quotientProjection y = C.quotientBasePoint :=
      (C.quotientBaseFiber y).mpr hyp
    exact hqne (hyq.symm.trans hbase)
  exact ⟨B, y, hynot, hconj⟩

end

end Theory.AlgebraicGroup.Bor1
