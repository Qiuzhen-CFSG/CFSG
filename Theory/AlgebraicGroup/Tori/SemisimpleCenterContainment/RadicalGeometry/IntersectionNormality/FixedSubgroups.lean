module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.Basic
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.FixedSubgroups.Connected
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.FixedSubgroups.Reduction
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.FixedSubgroups.ExternalFixedTangent
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.FixedSubgroups.ExternalWeights

/-!
External-torus fixed-subgroup tools for Borel III, 9.4--9.5 and IV, 13.16.

The acting torus only needs to normalize the subgroup. Its invariant tangent
decomposes into character spaces, and fixed tangents lift through the actual
fixed subgroups. Connected character kernels account for the nontrivial
weights; the full-torus fixed subgroup accounts for the trivial weight. These
facts prove an abstract subgroup-closure equality for every connected subgroup,
including the connected solvable groups used in 13.16. Keeping the full-torus
fixed subgroup also covers trivial actions and rank-zero tori.

The imported connectedness results apply to connected unipotent subgroups.
The generation and dimension theorems below discharge both tangent inputs of
`FixedSubgroups.Reduction` using the external conjugation action.

The dimension reduction treats `H/U` only through tangent dimensions. In
particular, it does not assume normality of `U` or form a quotient group.
Source: `refs/KGroup/Bor1/Chapter3.tex`, 9.4--9.5, and `Chapter4.tex`, 13.16.
-/

universe u

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The fixed tangents of a normalizing torus and its codimension-one subtori
span the tangent of the acted-on subgroup. -/
public theorem externalTorusFixed_tangent_span_of_normalizes
    {G : Variety k} [AlgebraicGroup G] (H T : ClosedSubgroup G)
    (hT : IsSubtorus T) (hTN : T ≤ H.normalizer) :
    closedSubgroupTangent H ≤
      closedSubgroupTangent (H.pointwiseCentralizer T) ⊔
        ⨆ Q : CodimensionOneSubtorus T,
          closedSubgroupTangent (H.pointwiseCentralizer Q.1) :=
  externalTorusFixed_tangent_span H T hT
    (hasExternalTangentWeightDecomposition_of_normalizes H T hT hTN)
    (hasExternalFixedTangentLifting_of_normalizes H T hTN)

/-- External-torus fixed-subgroup generation (Borel III, 9.5).
In particular this applies to connected solvable `H`; solvability is not
needed for generation. The full-torus fixed subgroup includes the trivial
action and rank-zero cases. -/
public theorem externalTorusFixed_generation
    {G : Variety k} [AlgebraicGroup G] (H T : ClosedSubgroup G)
    (hHc : _root_.IsConnected (H : Set (Variety.Point G)))
    (hT : IsSubtorus T) (hTN : T ≤ H.normalizer) :
    Subgroup.closure
      ((H.pointwiseCentralizer T : Set (Variety.Point G)) ∪
        ⋃ Q : CodimensionOneSubtorus T,
          (H.pointwiseCentralizer Q.1 : Set (Variety.Point G))) = H.toSubgroup :=
  externalTorusFixed_generation_of_tangent_inputs H T hHc hT
    (hasExternalTangentWeightDecomposition_of_normalizes H T hT hTN)
    (hasExternalFixedTangentLifting_of_normalizes H T hTN)

/-- The dimension implication used in Borel IV, 13.16. It applies, in
particular, to connected unipotent `H`, a connected closed subgroup `U ≤ H`
normalized by `T`, and a codimension-one subtorus `S ≤ T`. The tangent argument
only requires normalization of `H` and the three displayed local fixed-subgroup
inputs, so the conclusion holds for arbitrary closed `U` and `S` as well.
No relative normality of `U` or quotient-group structure on `H/U` is used. -/
public theorem externalTorusFixed_dimension_le
    {G : Variety k} [AlgebraicGroup G] (H U T S : ClosedSubgroup G)
    (hT : IsSubtorus T) (hTN : T ≤ H.normalizer)
    (hTU : H.pointwiseCentralizer T ≤ U)
    (hother : ∀ Q : CodimensionOneSubtorus T,
      Q.1 ≠ S → H.pointwiseCentralizer Q.1 ≤ U)
    (hlocal : Variety.dimension (H.pointwiseCentralizer S).carrierVariety ≤
      Variety.dimension ((H.pointwiseCentralizer S).inter U).carrierVariety + 1) :
    Variety.dimension H.carrierVariety ≤ Variety.dimension U.carrierVariety + 1 :=
  externalTorusFixed_dimension_le_of_tangent_inputs H U T S hT
    (hasExternalTangentWeightDecomposition_of_normalizes H T hT hTN)
    (hasExternalFixedTangentLifting_of_normalizes H T hTN) hTU hother hlocal

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality
