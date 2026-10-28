module

public import Stellmacher.MainType.Graph

/-!
# The distance-one Section Nine local type

Stellmacher's definition following (9.1) uses a pair with ambient Sylow
intersection and trivial two-core of its join. This module records every
local conclusion of that result: the wreath and SL2 quotients, Sylow order
128, the initial core equal to its center-generated subgroup, the quaternion
central product Vstar, and the order-eight subgroup with L3(2) normalizer
quotient in the original ambient group. The graph can belong to an injected
finite subgroup, while its normalizer witness and Sylow cardinal remain
in the ambient group. No global Hypothesis Two or identification with a
named finite group is part of the definition.

The original scan uses the regular wreath product and central product;
the LaTeX transcription's product symbols do not preserve those groups.
Source: Stellmacher, Journal of Algebra 190 (1997), (9.1), printed pp.46–48,
and its precise type definition on printed p.48.
-/

universe u

namespace Stellmacher

open Later SectionsFiveToSeven

/-- All source-local conclusions of (9.1), retaining the actual ambient
Sylow cardinal and full ambient normalizer of the order-eight subgroup. -/
public structure NineOneTypeData
    {H K : Type u} [Group H] [Finite H] [Group K] [Finite K]
    (embedding : K →* H) (sylow : Sylow 2 H)
    {S P1 P2 : Subgroup K}
    (Γ : CosetGraphContext.{u, u} K S P1 P2) (cp : CriticalPath Γ)
    (Vstar : Subgroup K) : Prop where
  critical_length : cp.length = 1
  definition : Vstar = conjugateClosure
    (ZAt Γ cp.a ⊓ QAt Γ cp.a') (GAt Γ cp.a')
  local_quotients :
    QuotientIsModel (GAt Γ cp.a) (QAt Γ cp.a) SL2TwoWreathC2 ∧
      QuotientIsModel (GAt Γ cp.a') (QAt Γ cp.a') SL2Two
  card_S : Nat.card sylow = 2 ^ 7
  initial_core : QAt Γ cp.a = ZAt Γ cp.a
  vstar_structure : IsCentralProductQ8Q8 Vstar
  normalizer_witness :
    ∃ U : Subgroup H,
      U ≤ Vstar.map embedding ∧ Nat.card U = 2 ^ 3 ∧
      QuotientIsModel (Subgroup.normalizer (U : Set H)) U L3Two

/-- The local pair at a and a' in the distance-one alternative (9.1). -/
public structure OmegaSixPlusTwoTypeData
    (H : Type u) [Group H] [Finite H] extends EmbeddedLocalTypeGraph H where
  intersection_eq :
    (GAt Γ criticalPath.a).map embedding ⊓
      (GAt Γ criticalPath.a').map embedding =
      (sylowIntersection : Subgroup H)
  join_twoCore_eq_bot :
    pCore 2 (↥((GAt Γ criticalPath.a).map embedding ⊔
      (GAt Γ criticalPath.a').map embedding)) = ⊥
  Vstar : Subgroup K
  caseData : NineOneTypeData embedding sylowIntersection Γ criticalPath Vstar

/-- A group is of type Ω₆⁺(2) when it contains the configuration (9.1). -/
@[expose] public def IsOfOmegaSixPlusTwoType
    (H : Type u) [Group H] [Finite H] : Prop :=
  Nonempty (OmegaSixPlusTwoTypeData H)

end Stellmacher
