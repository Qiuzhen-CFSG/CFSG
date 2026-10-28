module

public import Theory.AlgebraicGroup.Borel.Defs
public import Theory.AlgebraicGroup.Bor1.GeometricCertificates
public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.Tori.Basic
public import Theory.AlgebraicGroup.Unipotent.OneParameter

/-!
# Bor1, Chapter IV, Lemma 13.15

This module exports the exact source boundary needed by Theorem 13.16.  The
source calls `I(T)` the identity component of the intersection of the Borels
containing a maximal torus.  For distinct singular codimension-one subtori
`S,Q ≤ T`, Lemma 13.15 has two conclusions: the `S`-unipotent quotient of
`B` has dimension at most one modulo `I(T)_u`, and the `Q`-fixed part of
`I(B^S)` lies in `I(T)`.

The geometric inputs from Bor1 13.11--13.13 are imported from
`Bor1.GeometricCertificates`.  The package below keeps the two remaining
13.15 algebraic inputs explicit and provides a constructor which consumes one
combined geometric certificate rather than separate conditional Borel fields.
The additive quotient witness uses the proved one-parameter dimension API; the
centralizer inclusion is the subgroup-lattice argument from the source proof.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-! The source intersection `I(T) = (⋂_{B ∈ 𝓑^T} B)^0`. -/

public noncomputable def borelIntersection
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G) :
    ClosedSubgroup G :=
    ClosedSubgroup.ofSubgroup
    (⨅ B : BorelContainingIndex T, B.1.toSubgroup) (by
      simpa only [Subgroup.coe_iInf] using
        (isZariskiClosed_iInter (fun B : BorelContainingIndex T =>
          (B.1.toSubgroup : Set (Variety.Point G)))
          (fun B => B.1.isZariskiClosed)))

public noncomputable def borelIntersectionIdentityComponent
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G) :
    ClosedSubgroup G :=
  (borelIntersection T).identityComponentAmbient

/- The notation used by the source for the preceding subgroup. -/
public noncomputable def torusBorelIntersection
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G) :
    ClosedSubgroup G :=
  borelIntersectionIdentityComponent T

omit [IsAlgClosed k] in
/-- The intersection consists of the points in every Borel containing `T`.
This specification keeps the construction available across module boundaries. -/
public theorem borelIntersection_toSubgroup
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G) :
    (borelIntersection T).toSubgroup =
      ⨅ B : BorelContainingIndex T, B.1.toSubgroup := by rfl

/-- The source notation `I(T)` denotes the identity component of the actual
intersection of the Borels containing `T`. -/
public theorem torusBorelIntersection_eq_identityComponentAmbient
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G) :
    torusBorelIntersection T = (borelIntersection T).identityComponentAmbient := by rfl

/- A quotient of `U` by `N` presented by an additive algebraic character. -/
public structure OneDimensionalAdditiveQuotientWitness
    {G : Variety k} [AlgebraicGroup G]
    (U N : ClosedSubgroup G) where
  character : AlgebraicGroup.Morphism U.carrierVariety (KPlus k)
  surjective : Function.Surjective character.onPoints
  kernel_eq : character.kernelClosedSubgroup =
    U.inclusion.closedSubgroupPreimage N

/- The additive quotient witness has dimension at most one. -/
public theorem OneDimensionalAdditiveQuotientWitness.image_dimension_le_one
    {G : Variety k} [AlgebraicGroup G]
    {U N : ClosedSubgroup G}
    (w : OneDimensionalAdditiveQuotientWitness U N) :
    Variety.dimension w.character.imageClosedSubgroup.carrierVariety ≤ 1 := by
  calc
    Variety.dimension w.character.imageClosedSubgroup.carrierVariety ≤
        Variety.dimension (KPlus k) :=
      closedSubvariety_dimension_le (KPlus k)
        w.character.imageClosedSubgroup.isZariskiClosed
    _ = 1 := kPlus_dimension_eq_one

/-
If `A ≤ B ∩ B'` and the common `Q`-centralizer is in `I`, then the
`Q`-centralizer of `A` is in `I`.  This is the lattice step in 13.15(2).
-/
omit [IsAlgClosed k] in
public theorem pointwiseCentralizer_le_of_common_intersection
    {G : Variety k} [AlgebraicGroup G]
    (A B B' Q I : ClosedSubgroup G)
    (hA : A ≤ B.inter B')
    (hinter : (B.inter B').inter Q.centralizer ≤ I) :
    A.pointwiseCentralizer Q ≤ I := by
  intro x hx
  change x ∈ A.pointwiseCentralizer Q at hx
  have hxA : x ∈ A := (ClosedSubgroup.mem_inter_iff A Q.centralizer x).mp hx |>.1
  have hxQ : x ∈ Q.centralizer :=
    (ClosedSubgroup.mem_inter_iff A Q.centralizer x).mp hx |>.2
  apply hinter
  exact (ClosedSubgroup.mem_inter_iff (B.inter B') Q.centralizer x).mpr
    ⟨hA hxA, hxQ⟩

/- Data naming the singular codimension-one configuration of 13.15. -/
public structure Bor1Theorem13_15Setup
    {G : Variety k} [AlgebraicGroup G]
    (T B S Q : ClosedSubgroup G) where
  maximalTorus : IsMaximalTorus T
  borel : IsBorelSubgroup B
  torus_le_borel : T ≤ B
  S_subtorus : IsSubtorus S
  Q_subtorus : IsSubtorus Q
  S_le_T : S ≤ T
  Q_le_T : Q ≤ T
  S_singular : IsSingularSubtorus S
  Q_singular : IsSingularSubtorus Q
  S_codim_one : Variety.dimension S.carrierVariety + 1 =
    Variety.dimension T.carrierVariety
  Q_codim_one : Variety.dimension Q.carrierVariety + 1 =
    Variety.dimension T.carrierVariety
  distinct : S ≠ Q

/- The two source-faithful witness clauses of Bor1 13.15. -/
public structure Bor1Theorem13_15Package
    {G : Variety k} [AlgebraicGroup G]
    (T B S Q : ClosedSubgroup G)
    (setup : Bor1Theorem13_15Setup T B S Q)
    (B_u_S I_T_u I_B_S : ClosedSubgroup G) where
  B_u_S_le_B : B_u_S ≤ B
  I_T_u_le_B_u_S : I_T_u ≤ B_u_S
  quotient : OneDimensionalAdditiveQuotientWitness B_u_S I_T_u
  I_T_u_le_intersection : I_T_u ≤ torusBorelIntersection T
  geometry : Bor1Theorem13_11_13_13Certificate
    T B S Q I_B_S (torusBorelIntersection T)

/- Assemble the 13.15 package from the 13.11--13.13 witness data. -/
public def theorem_13_15
    {G : Variety k} [AlgebraicGroup G]
    {T B S Q : ClosedSubgroup G}
    (setup : Bor1Theorem13_15Setup T B S Q)
    (B_u_S I_T_u I_B_S : ClosedSubgroup G)
    (hB_u_S_le_B : B_u_S ≤ B)
    (hI_T_u_le_B_u_S : I_T_u ≤ B_u_S)
    (hquotient : OneDimensionalAdditiveQuotientWitness B_u_S I_T_u)
    (hI_T_u_le_intersection : I_T_u ≤ torusBorelIntersection T)
    (geometry : Bor1Theorem13_11_13_13Certificate
      T B S Q I_B_S (torusBorelIntersection T)) :
    Bor1Theorem13_15Package T B S Q setup B_u_S I_T_u I_B_S :=
  { B_u_S_le_B := hB_u_S_le_B
    I_T_u_le_B_u_S := hI_T_u_le_B_u_S
    quotient := hquotient
    I_T_u_le_intersection := hI_T_u_le_intersection
    geometry := geometry }

/- Compatibility projections for consumers of the former explicit witness API. -/
public noncomputable def Bor1Theorem13_15Package.witnessB'
    {G : Variety k} [AlgebraicGroup G]
    {T B S Q : ClosedSubgroup G}
    {setup : Bor1Theorem13_15Setup T B S Q}
    {B_u_S I_T_u I_B_S : ClosedSubgroup G}
    (h : Bor1Theorem13_15Package T B S Q setup B_u_S I_T_u I_B_S) :
    ClosedSubgroup G :=
  h.geometry.witnessB'

public theorem Bor1Theorem13_15Package.I_B_S_le_common
    {G : Variety k} [AlgebraicGroup G]
    {T B S Q : ClosedSubgroup G}
    {setup : Bor1Theorem13_15Setup T B S Q}
    {B_u_S I_T_u I_B_S : ClosedSubgroup G}
    (h : Bor1Theorem13_15Package T B S Q setup B_u_S I_T_u I_B_S) :
    I_B_S ≤ B.inter h.witnessB' :=
  h.geometry.iB_S_le_common'

public theorem Bor1Theorem13_15Package.q_common_le_I_T
    {G : Variety k} [AlgebraicGroup G]
    {T B S Q : ClosedSubgroup G}
    {setup : Bor1Theorem13_15Setup T B S Q}
    {B_u_S I_T_u I_B_S : ClosedSubgroup G}
    (h : Bor1Theorem13_15Package T B S Q setup B_u_S I_T_u I_B_S) :
    (B.inter h.witnessB').inter Q.centralizer ≤
      torusBorelIntersection T :=
  h.geometry.common_q_centralizer_le

/- The quotient-dimension conclusion exported to Theorem 13.16. -/
public theorem Bor1Theorem13_15Package.dimension_at_most_one
    {G : Variety k} [AlgebraicGroup G]
    {T B S Q : ClosedSubgroup G}
    {setup : Bor1Theorem13_15Setup T B S Q}
    {B_u_S I_T_u I_B_S : ClosedSubgroup G}
    (h : Bor1Theorem13_15Package T B S Q setup B_u_S I_T_u I_B_S) :
    Variety.dimension h.quotient.character.imageClosedSubgroup.carrierVariety ≤ 1 :=
  h.quotient.image_dimension_le_one

/- Alias using the quotient terminology of the source and Theorem 13.16. -/
public theorem Bor1Theorem13_15Package.quotient_dimension_le_one
    {G : Variety k} [AlgebraicGroup G]
    {T B S Q : ClosedSubgroup G}
    {setup : Bor1Theorem13_15Setup T B S Q}
    {B_u_S I_T_u I_B_S : ClosedSubgroup G}
    (h : Bor1Theorem13_15Package T B S Q setup B_u_S I_T_u I_B_S) :
    Variety.dimension h.quotient.character.imageClosedSubgroup.carrierVariety ≤ 1 :=
  h.dimension_at_most_one

/- The `Q`-centralizer inclusion exported to Theorem 13.16. -/
public theorem Bor1Theorem13_15Package.q_centralizer_le
    {G : Variety k} [AlgebraicGroup G]
    {T B S Q : ClosedSubgroup G}
    {setup : Bor1Theorem13_15Setup T B S Q}
    {B_u_S I_T_u I_B_S : ClosedSubgroup G}
    (h : Bor1Theorem13_15Package T B S Q setup B_u_S I_T_u I_B_S) :
    I_B_S.pointwiseCentralizer Q ≤ borelIntersectionIdentityComponent T :=
  pointwiseCentralizer_le_of_common_intersection
    I_B_S B h.geometry.witnessB' Q (borelIntersectionIdentityComponent T)
      h.geometry.iB_S_le_common' h.geometry.common_q_centralizer_le

end Theory.AlgebraicGroup
