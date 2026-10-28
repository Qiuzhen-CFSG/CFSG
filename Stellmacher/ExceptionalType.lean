module

public import Stellmacher.LaterDefs

/-!
# The four exceptional local types in Stellmacher's Theorem 2

The phrase “of type” in Theorem 2 refers to local pairs, not to an
isomorphism between the ambient group and a named simple group.  This module
records the four precise local configurations defined after (8.2), (8.6), and
(10.1): the `L₃(2)` and `Sp₄(2)` pairs, alternative (8.6)(a), and alternative
(10.1)(b).  Every pair supplies a Sylow 2-subgroup of the ambient group as its
intersection and has trivial 2-core in the subgroup it generates.

The last case follows the journal scan rather than the defective LaTeX
transcription: its common equality is
`W'_{a+2} = V_{a+1} ∩ V_{a'}`.  Accordingly, the two quotients involving that
intersection use `DerivedAmbient Wnext` as their denominator or numerator.
The graph records retain only the structural data occurring in the local-type
definitions; the global Hypothesis 2 assumptions used to prove the numbered
results are deliberately absent. Their graph group is embedded injectively in
the ambient group: a connected coset graph belongs to the generated local
group, which need not be the whole ambient group. All case equations remain
in that graph group, while the mapped pair has Sylow intersection and trivial
join 2-core in the original ambient group.

Source: `refs/latex/stellmacher-n-group.tex`, definitions following (8.2),
(8.6), and (10.1), checked against `refs/files/stellmacher-n-group.pdf`,
pp. 38, 45, and 65 (printed pagination).
-/

open scoped BigOperators Pointwise

universe u

namespace Stellmacher

open Later
open SectionsFiveToSeven

/-- The pair condition common to the paper's definitions of “type”.  The pair
itself supplies the Sylow 2-subgroup which occurs as its intersection. -/
public structure LocalTypePair
    (H : Type u) [Group H] [Finite H] : Type u where
  sylowIntersection : Sylow 2 H
  first : Subgroup H
  second : Subgroup H
  intersection_eq : first ⊓ second = (sylowIntersection : Subgroup H)
  join_twoCore_eq_bot : pCore 2 (↥(first ⊔ second)) = ⊥

/-- The source definition of a group of type `L₃(2)` following (8.2). -/
@[expose] public def IsOfL3TwoType
    (H : Type u) [Group H] [Finite H] : Prop :=
  ∃ p : LocalTypePair H,
    IsModel p.first S4 ∧ IsModel p.second S4

/-- The source definition of a group of type `Sp₄(2)` following (8.2). -/
@[expose] public def IsOfSp4TwoType
    (H : Type u) [Group H] [Finite H] : Prop :=
  ∃ p : LocalTypePair H,
    IsModel p.first (C2 × S4) ∧ IsModel p.second (C2 × S4)

/-- The common conclusions and case-(a) data in (8.6), without the global
Hypothesis 2 assumptions used to prove that result. -/
public structure EightSixCaseATypeData
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (Γ : CosetGraphContext.{u, u} H S P1 P2)
    (cp : CriticalPath Γ)
    (aPrev : Γ.Vertex) (D L Q T : Subgroup H) : Prop where
  previous_vertex : aPrev ∈ Neighborhood Γ cp.a ∧ aPrev ≠ cp.firstStep
  definitions :
    D = QAt Γ aPrev ⊓ QAt Γ cp.firstStep ∧
    L = conjugateClosure (QAt Γ aPrev) (GAt Γ cp.a) ∧
    Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt Γ cp.a)
  base : ⁅D, L⁆ = ZAt Γ cp.a ∧
    QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D
  card_S : 2 ^ 5 ≤ Nat.card S ∧ Nat.card S ≤ 2 ^ 6
  local_quotients : ∀ d : Γ.Vertex,
    QuotientIsModel (GAt Γ d) (QAt Γ d) SL2Two
  Q_eq : Q = QAt Γ cp.a
  twoCore_model : IsModel (twoCoreIn (EAt Γ cp.a)) (C4 × C4)
  generated : ∃ t : H,
    (t = 1 ∨ IsInvertingOn t (twoCoreIn (EAt Γ cp.a))) ∧
      Q = GeneratedWith (twoCoreIn (EAt Γ cp.a)) t
  next_twoCore :
    (IsCentralProductModel (QAt Γ cp.firstStep) C4 Q8 ∨
      IsCentralProductQ8Q8 (QAt Γ cp.firstStep)) ∧
    IsModel (QAt Γ cp.firstStep ⊓ EAt Γ cp.firstStep) Q8

/-- The local-pair realization of alternative (8.6)(a), which is the paper's
definition of type `G₂(2)'`. -/
public structure GTwoTwoDerivedTypeData
    (H : Type u) [Group H] [Finite H] where
  K : Type u
  [groupK : Group K]
  [finiteK : Finite K]
  embedding : K →* H
  embedding_injective : Function.Injective embedding
  sylowIntersection : Sylow 2 H
  S : Subgroup K
  P1 : Subgroup K
  P2 : Subgroup K
  Γ : CosetGraphContext.{u, u} K S P1 P2
  criticalPath : CriticalPath Γ
  intersection_eq :
    (GAt Γ criticalPath.a).map embedding ⊓
      (GAt Γ criticalPath.firstStep).map embedding =
      (sylowIntersection : Subgroup H)
  join_twoCore_eq_bot :
    pCore 2 (↥((GAt Γ criticalPath.a).map embedding ⊔
      (GAt Γ criticalPath.firstStep).map embedding)) = ⊥
  aPrev : Γ.Vertex
  D : Subgroup K
  L : Subgroup K
  Q : Subgroup K
  T : Subgroup K
  caseA : EightSixCaseATypeData Γ criticalPath aPrev D L Q T

/-- A group is of type `G₂(2)'` when it contains the local configuration in
alternative (8.6)(a). -/
@[expose] public def IsOfGTwoTwoDerivedType
    (H : Type u) [Group H] [Finite H] : Prop :=
  Nonempty (GTwoTwoDerivedTypeData H)

/-- The common conclusions and case-(b) data in the scan-correct statement of
(10.1).  The source's `W'_{a+2}` is `DerivedAmbient Wnext`. -/
public structure TenOneCaseBTypeData
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (Γ : CosetGraphContext.{u, u} H S P1 P2)
    (cp : CriticalPath Γ)
    (aPlus2 : Γ.Vertex) (W W0 Wnext : Subgroup H) : Prop where
  critical_length : cp.length = 3
  path_offset : IsCriticalPathOffset Γ cp 2 aPlus2
  definitions :
    W = conjugateClosure (VAt Γ cp.firstStep ⊓ QAt Γ cp.a')
      (GAt Γ aPlus2) ∧
    Wnext = GeneratedNeighborhoodV Γ aPlus2 ∧
    W0 = NeighborhoodQIntersection Γ (Neighborhood Γ aPlus2) ⊓ Wnext
  derived_intersection :
    DerivedAmbient Wnext = VAt Γ cp.firstStep ⊓ VAt Γ cp.a'
  index_conclusions :
    QuotientCardEq W0 W 2 ∧ QuotientCardEq Wnext W (2 ^ 3)
  card_S : 2 ^ 11 ≤ Nat.card S ∧ Nat.card S ≤ 2 ^ 12
  local_quotients :
    QuotientIsModel (GAt Γ aPlus2) (QAt Γ aPlus2) SL2Two ∧
    QuotientIsFrobenius20 (GAt Γ cp.firstStep) (QAt Γ cp.firstStep)
  first_step_structure :
    QuotientCardEq (VAt Γ cp.firstStep) (ZAt Γ cp.firstStep) (2 ^ 4) ∧
    QuotientCardEq (twoCoreIn (EAt Γ cp.firstStep))
      (VAt Γ cp.firstStep) (2 ^ 4) ∧
    DerivedAmbient (twoCoreIn (EAt Γ cp.firstStep)) = VAt Γ cp.firstStep
  remaining_indices :
    Nat.card (ZAt Γ aPlus2) = 4 ∧
    QuotientCardEq W (DerivedAmbient Wnext) 4 ∧
    QuotientCardEq Wnext W0 4 ∧
    QuotientCardEq (twoCoreIn (EAt Γ aPlus2) ⊔ Wnext) Wnext 4 ∧
    QuotientCardEq (DerivedAmbient Wnext) (ZAt Γ aPlus2) 2

/-- The local-pair realization of alternative (10.1)(b), which is the paper's
definition of type `²F₄(2)'`. -/
public structure TwistedF4TwoDerivedTypeData
    (H : Type u) [Group H] [Finite H] where
  K : Type u
  [groupK : Group K]
  [finiteK : Finite K]
  embedding : K →* H
  embedding_injective : Function.Injective embedding
  sylowIntersection : Sylow 2 H
  S : Subgroup K
  P1 : Subgroup K
  P2 : Subgroup K
  Γ : CosetGraphContext.{u, u} K S P1 P2
  criticalPath : CriticalPath Γ
  aPlus2 : Γ.Vertex
  intersection_eq :
    (GAt Γ aPlus2).map embedding ⊓
      (GAt Γ criticalPath.firstStep).map embedding =
      (sylowIntersection : Subgroup H)
  join_twoCore_eq_bot :
    pCore 2 (↥((GAt Γ aPlus2).map embedding ⊔
      (GAt Γ criticalPath.firstStep).map embedding)) = ⊥
  W : Subgroup K
  W0 : Subgroup K
  Wnext : Subgroup K
  caseB : TenOneCaseBTypeData Γ criticalPath aPlus2 W W0 Wnext

/-- A group is of type `²F₄(2)'` when it contains the local configuration in
alternative (10.1)(b). -/
@[expose] public def IsOfTwistedF4TwoDerivedType
    (H : Type u) [Group H] [Finite H] : Prop :=
  Nonempty (TwistedF4TwoDerivedTypeData H)

/-- The source-faithful meaning of alternative (a) of Stellmacher's Theorem 2:
the ambient group contains one of the four specified local configurations. -/
@[expose] public def IsOfExceptionalType
    (H : Type u) [Group H] [Finite H] : Prop :=
  IsOfL3TwoType H ∨ IsOfSp4TwoType H ∨
    IsOfGTwoTwoDerivedType H ∨ IsOfTwistedF4TwoDerivedType H

end Stellmacher
