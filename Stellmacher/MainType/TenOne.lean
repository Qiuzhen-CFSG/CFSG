module
public import Stellmacher.MainType.Graph

/-!
# The small Section Ten local configuration

The case record retains the common equations and the full small alternative in
Stellmacher (10.1), together with critical length three and the vertex at
offset two. Its order bound is on the supplied ambient Sylow subgroup. The
involution lies in the graph group, while its nonsolvable centralizer is
in the original ambient group. No global Hypothesis Two or recognition of a
named finite group is assumed. The source's derived group of the generated
neighborhood is recorded literally as `DerivedAmbient Wnext`.

The type record embeds this configuration into the ambient group and retains
its source pair at a+2 and a+1. Their mapped intersection is the supplied
ambient Sylow, and the join of their images has trivial two-core. These are
local structural definitions; the graph group need not be the whole ambient
group, and no named finite-group model is included in the witness.

Source: Stellmacher, Journal of Algebra 190 (1997), (10.1)(a), printed
pp.59–65, and the definition of type M12 following that result.
-/

namespace Stellmacher
open Later SectionsFiveToSeven
universe u

/-- The common conclusions and complete small alternative of (10.1), with
an ambient Sylow order bound and ambient involution centralizer. -/
public structure TenOneCaseATypeData
    {H K : Type u} [Group H] [Finite H] [Group K] [Finite K]
    (embedding : K →* H) (sylow : Sylow 2 H)
    {S P1 P2 : Subgroup K}
    (Γ : CosetGraphContext.{u,u} K S P1 P2) (cp : CriticalPath Γ)
    (aPlus2 : Γ.Vertex) (W W0 Wnext : Subgroup K) : Prop where
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
  card_S : 2 ^ 6 ≤ Nat.card sylow ∧ Nat.card sylow ≤ 2 ^ 7
  local_quotients :
    QuotientIsModel (GAt Γ cp.firstStep) (QAt Γ cp.firstStep) SL2Two ∧
    QuotientIsModel (GAt Γ aPlus2) (QAt Γ aPlus2) SL2Two
  middle_structure :
    ZAt Γ aPlus2 = W ∧ IsModel (twoCoreIn (EAt Γ aPlus2)) (C4 × C4)
  first_step_structure :
    Nat.card (VAt Γ cp.firstStep) = 2 ^ 3 ∧
    IsExtraspecial 2 (↥(twoCoreIn (EAt Γ cp.firstStep))) ∧
    Nat.card (twoCoreIn (EAt Γ cp.firstStep)) = 2 ^ 5
  nonsolvable_centralizer :
    ∃ point : K,
      Later.IsInvolution point ∧ point ∈ QAt Γ aPlus2 ∧ point ∉ ZAt Γ aPlus2 ∧
      ¬ Group.IsSolvable (Subgroup.centralizer ({embedding point} : Set H))

/-- The embedded source local pair at a+2 and a+1 in alternative (10.1)(a). -/
public structure MathieuTwelveTypeData
    (H : Type u) [Group H] [Finite H] extends EmbeddedLocalTypeGraph H where
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
  caseA : TenOneCaseATypeData embedding sylowIntersection Γ criticalPath aPlus2 W W0 Wnext

/-- A group is of type M12 when it contains the source configuration (10.1)(a). -/
@[expose] public def IsOfMathieuTwelveType
    (H : Type u) [Group H] [Finite H] : Prop :=
  Nonempty (MathieuTwelveTypeData H)

end Stellmacher
