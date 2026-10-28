module
public import Stellmacher.MainType.Graph

/-!
# The two remaining Section Eight local types

The common conclusions of (8.6), together with every field of alternatives
(b) and (c), are recorded without global hypotheses. These are structural
local configurations in a finite graph group. In particular the three-Sylow
T is the prescribed subgroup in every fixed-point conclusion, and the final
normalizers remain those of the graph group. The named type records embed
this graph group into the ambient group, give the literal a/a+1 pair its
ambient Sylow intersection and trivial join two-core, and explicitly equate
the native S cardinal with that of the ambient Sylow. Their bounds therefore
concern the actual ambient Sylow. These definitions make no claim that the
ambient group is isomorphic to either named example.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6), printed p.41,
and the type definition on printed p.45. The two action fields of case (c)
retain the approved quotient-fixed-coset and suitable-involution-lift meanings.
-/

namespace Stellmacher
open Later SectionsFiveToSeven
universe u

/-- The definitions and common conclusions preceding alternatives (8.6)(a–c). -/
public structure EightSixCommonTypeData
    {K : Type u} [Group K] [Finite K]
    {S P1 P2 : Subgroup K}
    (Γ : CosetGraphContext.{u,u} K S P1 P2) (cp : CriticalPath Γ)
    (aPrev : Γ.Vertex) (D L Q T : Subgroup K) : Prop where
  previous_vertex : aPrev ∈ Neighborhood Γ cp.a ∧ aPrev ≠ cp.firstStep
  definitions :
    D = QAt Γ aPrev ⊓ QAt Γ cp.firstStep ∧
    L = conjugateClosure (QAt Γ aPrev) (GAt Γ cp.a) ∧
    Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt Γ cp.a)
  base : ⁅D,L⁆ = ZAt Γ cp.a ∧
    QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D

/-- All structural conclusions of (8.6)(b), with its native graph subgroup S. -/
public structure EightSixCaseBTypeData
    {K : Type u} [Group K] [Finite K]
    {S P1 P2 : Subgroup K}
    (Γ : CosetGraphContext.{u,u} K S P1 P2) (cp : CriticalPath Γ)
    (aPrev : Γ.Vertex) (D L Q T : Subgroup K) : Prop
    extends EightSixCommonTypeData Γ cp aPrev D L Q T where
  card_S : 2 ^ 8 ≤ Nat.card S ∧ Nat.card S ≤ 2 ^ 10
  initial_quotient : QuotientIsModel (GAt Γ cp.a) (QAt Γ cp.a) SL2Two
  next_quotient : QuotientIsModel (GAt Γ cp.firstStep)
    (QAt Γ cp.firstStep) SL2TwoWreathC2
  initial_core :
    QuotientOrderLe Q (twoCoreIn (EAt Γ cp.a)) 4 ∧
    IsSpecialTwo (twoCoreIn (EAt Γ cp.a)) ∧
    Nat.card (twoCoreIn (EAt Γ cp.a)) = 2 ^ 6 ∧
    twoCoreIn (EAt Γ cp.a) ⊓ Subgroup.centralizer (T : Set K) = ⊥
  next_core : IsCentralProductQ8Q8 (VAt Γ cp.firstStep) ∧
    FrattiniAmbient (QAt Γ cp.firstStep) = ZAt Γ cp.firstStep
  normalizer_witness : ∃ W : Subgroup K,
    W ≤ L ∧ (W.subgroupOf L).Normal ∧
    IsElementaryAbelianSubgroup 2 W ∧ Nat.card W = 2 ^ 4 ∧
    IsNonsolvableNormalizer W

/-- All structural conclusions of (8.6)(c), including the approved quotient actions. -/
public structure EightSixCaseCTypeData
    {K : Type u} [Group K] [Finite K]
    {S P1 P2 : Subgroup K}
    (Γ : CosetGraphContext.{u,u} K S P1 P2) (cp : CriticalPath Γ)
    (aPrev : Γ.Vertex) (D L Q T : Subgroup K) : Prop
    extends EightSixCommonTypeData Γ cp aPrev D L Q T where
  card_S : 2 ^ 14 ≤ Nat.card S ∧ Nat.card S ≤ 2 ^ 15
  initial_quotient : QuotientIsModel (GAt Γ cp.a) (QAt Γ cp.a) SL2Two
  next_residual : QuotientElementaryAbelian (EAt Γ cp.firstStep)
    (twoCoreIn (EAt Γ cp.firstStep)) 3 4
  initial_core : QuotientCardEq Q D (2 ^ 6) ∧ Nat.card D = 2 ^ 5 ∧
    Nat.card (ZAt Γ cp.a) = 4 ∧
    IsInternalDirectProductTwo D (Q ⊓ Subgroup.centralizer (T : Set K)) (ZAt Γ cp.a)
  next_core : IsExtraspecial 2 (↥(QAt Γ cp.firstStep)) ∧
    Nat.card (QAt Γ cp.firstStep) = 2 ^ 9 ∧
    QuotientElementaryAbelian Q (Q ⊓ QAt Γ cp.firstStep) 2 3
  quotient_three_action : QuotientQInvariantOrderThreeFixedPointFree
    (EAt Γ cp.firstStep) (twoCoreIn (EAt Γ cp.firstStep))
    Q (ZAt Γ cp.firstStep) (QAt Γ cp.firstStep)
  quotient_involution_action : QuotientInvolutionCentralizes Q (QAt Γ cp.firstStep)
  normalizer_quotient : ∃ lam : Γ.Vertex,
    lam ∈ Neighborhood Γ cp.firstStep ∧ lam ≠ cp.a ∧
    QuotientIsModel
      (Subgroup.normalizer ((ZAt Γ lam ⊔ ZAt Γ cp.a : Subgroup K) : Set K))
      (Subgroup.centralizer ((ZAt Γ lam ⊔ ZAt Γ cp.a : Subgroup K) : Set K)) L3Two

/-- The source-local realization of (8.6)(b), with its actual ambient Sylow pair. -/
public structure OmegaSixMinusThreeTypeData
    (H : Type u) [Group H] [Finite H] extends EmbeddedLocalTypeGraph H where
  intersection_eq :
    (GAt Γ criticalPath.a).map embedding ⊓
      (GAt Γ criticalPath.firstStep).map embedding =
      (sylowIntersection : Subgroup H)
  join_twoCore_eq_bot :
    pCore 2 (↥((GAt Γ criticalPath.a).map embedding ⊔
      (GAt Γ criticalPath.firstStep).map embedding)) = ⊥
  sylow_card_eq : Nat.card S = Nat.card sylowIntersection
  aPrev : Γ.Vertex
  D : Subgroup K
  L : Subgroup K
  Q : Subgroup K
  T : Subgroup K
  caseB : EightSixCaseBTypeData Γ criticalPath aPrev D L Q T

/-- The type Ω₆⁻(3) means the local configuration in (8.6)(b). -/
@[expose] public def IsOfOmegaSixMinusThreeType
    (H : Type u) [Group H] [Finite H] : Prop :=
  Nonempty (OmegaSixMinusThreeTypeData H)

/-- The source-local realization of (8.6)(c), with its actual ambient Sylow pair. -/
public structure OmegaEightPlusThreeTypeData
    (H : Type u) [Group H] [Finite H] extends EmbeddedLocalTypeGraph H where
  intersection_eq :
    (GAt Γ criticalPath.a).map embedding ⊓
      (GAt Γ criticalPath.firstStep).map embedding =
      (sylowIntersection : Subgroup H)
  join_twoCore_eq_bot :
    pCore 2 (↥((GAt Γ criticalPath.a).map embedding ⊔
      (GAt Γ criticalPath.firstStep).map embedding)) = ⊥
  sylow_card_eq : Nat.card S = Nat.card sylowIntersection
  aPrev : Γ.Vertex
  D : Subgroup K
  L : Subgroup K
  Q : Subgroup K
  T : Subgroup K
  caseC : EightSixCaseCTypeData Γ criticalPath aPrev D L Q T

/-- The type Ω₈⁺(3) means the local configuration in (8.6)(c). -/
@[expose] public def IsOfOmegaEightPlusThreeType
    (H : Type u) [Group H] [Finite H] : Prop :=
  Nonempty (OmegaEightPlusThreeTypeData H)

end Stellmacher
