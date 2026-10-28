module

public import Theory.AlgebraicGroup.Borel.Defs
public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.Radical.Defs
public import Theory.AlgebraicGroup.Semisimple.Defs
public import Theory.AlgebraicGroup.Tori.Basic

/-!
# Bor1, Chapter IV, Lemmas 13.11--13.13

This module is the lower geometric boundary for the singular-torus argument.
The source proves that the centralizer of a singular codimension-one subtorus
has a semisimple quotient of rank one, that two distinct singular subtori can
be separated by a second torus-containing Borel, and that the resulting
common fixed centralizer is contained in the Borel intersection `I(T)`.  The
ambient development does not yet contain the preceding quotient and Borel
existence theorems, so these facts are exported as one source-faithful,
placeholder-free certificate.  The certificate records only the geometric
data consumed by Lemma 13.15; its lattice consequences are proved in
`SingularTorusQuotient`.

The displayed conclusion in the source's 13.12 corollary has a typographical
error.  The field below uses the mathematically intended statement
`B'^Q ≠ B^Q`.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/- The subgroup of `A` fixed pointwise by `Q`. -/
@[expose]
public def ClosedSubgroup.pointwiseCentralizer
    {G : Variety k} [AlgebraicGroup G]
    (A Q : ClosedSubgroup G) : ClosedSubgroup G :=
  A.inter Q.centralizer

/- Borels containing a prescribed closed subgroup. -/
public abbrev BorelContainingIndex
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G) :=
  {B : ClosedSubgroup G // IsBorelSubgroup B ∧ S ≤ B}

/- A torus is singular when infinitely many Borels contain it. -/
public def IsSingularSubtorus
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G) : Prop :=
  Infinite (BorelContainingIndex S)

/-!
The quotient part of 13.11/13.13.  The quotient is required to be semisimple,
and one of its maximal tori is required to have dimension one.  This is the
intrinsic rank-one condition and avoids committing lower layers to a chosen
`PGL₂` carrier.
-/
public structure SemisimpleRankOneQuotientCertificate
    {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) where
  quotient : Variety k
  quotientAlgebraicGroup : AlgebraicGroup quotient
  quotientMap : @AlgebraicGroup.Morphism k _ H.carrierVariety quotient
    H.carrierAlgebraicGroup quotientAlgebraicGroup
  surjective : Function.Surjective quotientMap.onPoints
  radical : ClosedSubgroup H.carrierVariety
  radical_isRadical : IsRadicalSubgroup radical
  kernel_eq_radical : quotientMap.kernelClosedSubgroup = radical
  quotient_isSemisimple : IsSemisimpleAlgebraicGroup quotient
  quotientTorus : ClosedSubgroup quotient
  quotientTorus_isMaximal : IsMaximalTorus quotientTorus
  quotientTorus_dimension :
    Variety.dimension quotientTorus.carrierVariety = 1

/-!
The rank-one semisimple quotient certificate for a singular codimension-one
centralizer.  The maximal-torus containment is kept here because it is the
part of 13.11 used to compare the centralizer Weyl chambers with those of the
ambient group.
-/
public structure Bor1Theorem13_11Certificate
    {G : Variety k} [AlgebraicGroup G]
    (T S : ClosedSubgroup G) where
  maximalTorus : IsMaximalTorus T
  subtorus : IsSubtorus S
  subtorus_le_torus : S ≤ T
  singular : IsSingularSubtorus S
  codim_one : Variety.dimension S.carrierVariety + 1 =
    Variety.dimension T.carrierVariety
  torus_le_centralizer : T ≤ S.centralizer
  rankOneQuotient : SemisimpleRankOneQuotientCertificate S.centralizer

/-!
The Borel witness of 13.12.  Both Borels contain `T`; equality on the `S`
fixed Borel and inequality on the `Q` fixed Borel are recorded explicitly.
-/
public structure Bor1Theorem13_12Certificate
    {G : Variety k} [AlgebraicGroup G]
    (T B S Q : ClosedSubgroup G) where
  source_isBorel : IsBorelSubgroup B
  torus_le_source : T ≤ B
  witnessB' : ClosedSubgroup G
  witness_isBorel : IsBorelSubgroup witnessB'
  torus_le_witness : T ≤ witnessB'
  s_restriction_eq : witnessB'.pointwiseCentralizer S =
    B.pointwiseCentralizer S
  q_restriction_ne : witnessB'.pointwiseCentralizer Q ≠
    B.pointwiseCentralizer Q

/-!
The rank-one intersection consequence used in 13.15.  `I` is normally
`I(T)`, the identity component of the intersection of all `T`-containing
Borels.
-/
public structure Bor1Theorem13_13Certificate
    {G : Variety k} [AlgebraicGroup G]
    (B B' Q I : ClosedSubgroup G) where
  q_borels_distinct : B.pointwiseCentralizer Q ≠
    B'.pointwiseCentralizer Q
  common_q_centralizer_le : (B.inter B').inter Q.centralizer ≤ I

/-!
All geometric data needed to instantiate Theorem 13.15.  The fields are
organized by source number, while the final containment is the direct
subgroup inclusion used by the 13.15 lattice step.
-/
public structure Bor1Theorem13_11_13_13Certificate
    {G : Variety k} [AlgebraicGroup G]
    (T B S Q I_B_S I_T : ClosedSubgroup G) where
  theorem_13_11 : Bor1Theorem13_11Certificate T S
  theorem_13_11_Q : Bor1Theorem13_11Certificate T Q
  theorem_13_12 : Bor1Theorem13_12Certificate T B S Q
  theorem_13_13 : Bor1Theorem13_13Certificate
    B theorem_13_12.witnessB' Q I_T
  iB_S_le_common : I_B_S ≤ B.inter theorem_13_12.witnessB'

/- Construct the combined certificate from the three source-numbered pieces. -/
public def Bor1Theorem13_11_13_13Certificate.of_witnesses
    {G : Variety k} [AlgebraicGroup G]
    {T B S Q I_B_S I_T : ClosedSubgroup G}
    (h11 : Bor1Theorem13_11Certificate T S)
    (h11Q : Bor1Theorem13_11Certificate T Q)
    (h12 : Bor1Theorem13_12Certificate T B S Q)
    (h13 : Bor1Theorem13_13Certificate B h12.witnessB' Q I_T)
    (hI : I_B_S ≤ B.inter h12.witnessB') :
    Bor1Theorem13_11_13_13Certificate T B S Q I_B_S I_T :=
  { theorem_13_11 := h11
    theorem_13_11_Q := h11Q
    theorem_13_12 := h12
    theorem_13_13 := h13
    iB_S_le_common := hI }

/-! Projection lemmas keep consumers independent of the nested record layout. -/

public def Bor1Theorem13_11_13_13Certificate.witnessB'
    {G : Variety k} [AlgebraicGroup G]
    {T B S Q I_B_S I_T : ClosedSubgroup G}
    (C : Bor1Theorem13_11_13_13Certificate T B S Q I_B_S I_T) :
    ClosedSubgroup G :=
  C.theorem_13_12.witnessB'

omit [IsAlgClosed k] in
public theorem Bor1Theorem13_11_13_13Certificate.iB_S_le_common'
    {G : Variety k} [AlgebraicGroup G]
    {T B S Q I_B_S I_T : ClosedSubgroup G}
    (C : Bor1Theorem13_11_13_13Certificate T B S Q I_B_S I_T) :
    I_B_S ≤ B.inter C.witnessB' :=
  C.iB_S_le_common

omit [IsAlgClosed k] in
public theorem Bor1Theorem13_11_13_13Certificate.common_q_centralizer_le
    {G : Variety k} [AlgebraicGroup G]
    {T B S Q I_B_S I_T : ClosedSubgroup G}
    (C : Bor1Theorem13_11_13_13Certificate T B S Q I_B_S I_T) :
    (B.inter C.witnessB').inter Q.centralizer ≤ I_T :=
  C.theorem_13_13.common_q_centralizer_le

end Theory.AlgebraicGroup
