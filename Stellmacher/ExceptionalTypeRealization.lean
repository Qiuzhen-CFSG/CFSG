module

public import Stellmacher.ExceptionalType

/-!
# Realizing embedded exceptional local configurations

The definitions following Stellmacher (8.6) and (10.1) ask for pairs contained
in H, not pairs generating H. These bridges accept all the existing local
case data in a finite graph group K and an injective homomorphism K →* H.
They retain the specified Sylow intersection in H. The native join maps
isomorphically to the join of the images, so `pCore_map_iso` transports its
trivial two-core; injectivity also identifies the mapped intersection.

Subgroup constructors apply directly to the generated join and the restricted
ambient Sylow subgroup. Identity constructors preserve the former same-ambient
realizations. The final projections recover the actual `LocalTypePair H`.
No terminal classification theorem or global Hypothesis Two is assumed.

Source: `refs/latex/stellmacher-n-group.tex`, definitions following (8.6)
and (10.1); all scan-correct case equations are in `ExceptionalType.lean`.
-/

universe u

namespace Stellmacher

open Later SectionsFiveToSeven

private theorem mapped_join_twoCore_eq_bot
    {H K : Type u} [Group H] [Group K]
    (embedding : K →* H) (hinjective : Function.Injective embedding)
    (first second : Subgroup K)
    (hcore : pCore 2 (↥(first ⊔ second)) = ⊥) :
    pCore 2 (↥(first.map embedding ⊔ second.map embedding)) = ⊥ := by
  rw [← Subgroup.map_sup]
  have hmap := pCore_map_iso 2
    ((first ⊔ second).equivMapOfInjective embedding hinjective)
  rw [hcore, Subgroup.map_bot] at hmap
  exact hmap.symm

/-- Realize the supplied (8.6)(a) configuration in its original ambient group.
The graph group can be the generated subgroup, without generating H. -/
public theorem isOfGTwoTwoDerivedType_of_embedded_caseA
    {H K : Type u} [Group H] [Finite H] [Group K] [Finite K]
    (embedding : K →* H) (hinjective : Function.Injective embedding)
    (sylow : Sylow 2 H) {S P1 P2 : Subgroup K}
    (graph : CosetGraphContext.{u, u} K S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q T : Subgroup K)
    (hintersection : (GAt graph path.a ⊓ GAt graph path.firstStep).map embedding =
      (sylow : Subgroup H))
    (hcore : pCore 2 (↥(GAt graph path.a ⊔ GAt graph path.firstStep)) = ⊥)
    (hcase : EightSixCaseATypeData graph path previous D L Q T) :
    IsOfGTwoTwoDerivedType H := by
  exact ⟨{
    K := K
    embedding := embedding
    embedding_injective := hinjective
    sylowIntersection := sylow
    S := S
    P1 := P1
    P2 := P2
    Γ := graph
    criticalPath := path
    intersection_eq := (Subgroup.map_inf _ _ embedding hinjective).symm.trans hintersection
    join_twoCore_eq_bot := mapped_join_twoCore_eq_bot embedding hinjective _ _ hcore
    aPrev := previous
    D := D
    L := L
    Q := Q
    T := T
    caseA := hcase }⟩

/-- Realize the supplied scan-correct (10.1)(b) data through an embedding. -/
public theorem isOfTwistedF4TwoDerivedType_of_embedded_caseB
    {H K : Type u} [Group H] [Finite H] [Group K] [Finite K]
    (embedding : K →* H) (hinjective : Function.Injective embedding)
    (sylow : Sylow 2 H) {S P1 P2 : Subgroup K}
    (graph : CosetGraphContext.{u, u} K S P1 P2) (path : CriticalPath graph)
    (next : graph.Vertex) (W W0 Wnext : Subgroup K)
    (hintersection : (GAt graph next ⊓ GAt graph path.firstStep).map embedding =
      (sylow : Subgroup H))
    (hcore : pCore 2 (↥(GAt graph next ⊔ GAt graph path.firstStep)) = ⊥)
    (hcase : TenOneCaseBTypeData graph path next W W0 Wnext) :
    IsOfTwistedF4TwoDerivedType H := by
  exact ⟨{
    K := K
    embedding := embedding
    embedding_injective := hinjective
    sylowIntersection := sylow
    S := S
    P1 := P1
    P2 := P2
    Γ := graph
    criticalPath := path
    aPlus2 := next
    intersection_eq := (Subgroup.map_inf _ _ embedding hinjective).symm.trans hintersection
    join_twoCore_eq_bot := mapped_join_twoCore_eq_bot embedding hinjective _ _ hcore
    W := W
    W0 := W0
    Wnext := Wnext
    caseB := hcase }⟩

/-- In particular the graph may live on a subgroup J (such as the generated
join), while its distinguished intersection is the restriction of a Sylow of H. -/
public theorem isOfGTwoTwoDerivedType_of_subgroup_caseA
    {H : Type u} [Group H] [Finite H]
    (sylow : Sylow 2 H) (J : Subgroup H) (hSylow : (sylow : Subgroup H) ≤ J)
    {S P1 P2 : Subgroup J}
    (graph : CosetGraphContext.{u, u} J S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q T : Subgroup J)
    (hintersection : GAt graph path.a ⊓ GAt graph path.firstStep =
      (sylow : Subgroup H).subgroupOf J)
    (hcore : pCore 2 (↥(GAt graph path.a ⊔ GAt graph path.firstStep)) = ⊥)
    (hcase : EightSixCaseATypeData graph path previous D L Q T) :
    IsOfGTwoTwoDerivedType H := by
  apply isOfGTwoTwoDerivedType_of_embedded_caseA J.subtype Subtype.val_injective
    sylow graph path previous D L Q T _ hcore hcase
  rw [hintersection, Subgroup.map_subgroupOf_eq_of_le hSylow]

/-- The subgroup realization of the scan-correct case (10.1)(b) retains the
ambient Sylow witness and transports the trivial core of the actual pair's join. -/
public theorem isOfTwistedF4TwoDerivedType_of_subgroup_caseB
    {H : Type u} [Group H] [Finite H]
    (sylow : Sylow 2 H) (J : Subgroup H) (hSylow : (sylow : Subgroup H) ≤ J)
    {S P1 P2 : Subgroup J}
    (graph : CosetGraphContext.{u, u} J S P1 P2) (path : CriticalPath graph)
    (next : graph.Vertex) (W W0 Wnext : Subgroup J)
    (hintersection : GAt graph next ⊓ GAt graph path.firstStep =
      (sylow : Subgroup H).subgroupOf J)
    (hcore : pCore 2 (↥(GAt graph next ⊔ GAt graph path.firstStep)) = ⊥)
    (hcase : TenOneCaseBTypeData graph path next W W0 Wnext) :
    IsOfTwistedF4TwoDerivedType H := by
  apply isOfTwistedF4TwoDerivedType_of_embedded_caseB J.subtype Subtype.val_injective
    sylow graph path next W W0 Wnext _ hcore hcase
  rw [hintersection, Subgroup.map_subgroupOf_eq_of_le hSylow]

/-- Compatibility construction for a former same-ambient (8.6)(a) realization. -/
public theorem isOfGTwoTwoDerivedType_of_eightSix_caseA
    {H : Type u} [Group H] [Finite H]
    (sylow : Sylow 2 H) {S P1 P2 : Subgroup H}
    (graph : CosetGraphContext.{u, u} H S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q T : Subgroup H)
    (hintersection : GAt graph path.a ⊓ GAt graph path.firstStep =
      (sylow : Subgroup H))
    (hcore : pCore 2 (↥(GAt graph path.a ⊔ GAt graph path.firstStep)) = ⊥)
    (hcase : EightSixCaseATypeData graph path previous D L Q T) :
    IsOfGTwoTwoDerivedType H := by
  exact isOfGTwoTwoDerivedType_of_embedded_caseA (MonoidHom.id H)
    Function.injective_id sylow graph path previous D L Q T
    (by simpa using hintersection) hcore hcase

/-- Compatibility construction for a former same-ambient (10.1)(b) realization. -/
public theorem isOfTwistedF4TwoDerivedType_of_tenOne_caseB
    {H : Type u} [Group H] [Finite H]
    (sylow : Sylow 2 H) {S P1 P2 : Subgroup H}
    (graph : CosetGraphContext.{u, u} H S P1 P2) (path : CriticalPath graph)
    (next : graph.Vertex) (W W0 Wnext : Subgroup H)
    (hintersection : GAt graph next ⊓ GAt graph path.firstStep =
      (sylow : Subgroup H))
    (hcore : pCore 2 (↥(GAt graph next ⊔ GAt graph path.firstStep)) = ⊥)
    (hcase : TenOneCaseBTypeData graph path next W W0 Wnext) :
    IsOfTwistedF4TwoDerivedType H := by
  exact isOfTwistedF4TwoDerivedType_of_embedded_caseB (MonoidHom.id H)
    Function.injective_id sylow graph path next W W0 Wnext
    (by simpa using hintersection) hcore hcase

/-- The (8.6)(a) witness supplies a genuine local pair in H, not merely in K. -/
@[expose] public def GTwoTwoDerivedTypeData.toLocalTypePair
    {H : Type u} [Group H] [Finite H] (data : GTwoTwoDerivedTypeData H) :
    LocalTypePair H := by
  letI := data.groupK
  letI := data.finiteK
  exact {
    sylowIntersection := data.sylowIntersection
    first := (GAt data.Γ data.criticalPath.a).map data.embedding
    second := (GAt data.Γ data.criticalPath.firstStep).map data.embedding
    intersection_eq := data.intersection_eq
    join_twoCore_eq_bot := data.join_twoCore_eq_bot }

/-- The (10.1)(b) witness supplies the source's pair at a+2 and a+1 in H. -/
@[expose] public def TwistedF4TwoDerivedTypeData.toLocalTypePair
    {H : Type u} [Group H] [Finite H] (data : TwistedF4TwoDerivedTypeData H) :
    LocalTypePair H := by
  letI := data.groupK
  letI := data.finiteK
  exact {
    sylowIntersection := data.sylowIntersection
    first := (GAt data.Γ data.aPlus2).map data.embedding
    second := (GAt data.Γ data.criticalPath.firstStep).map data.embedding
    intersection_eq := data.intersection_eq
    join_twoCore_eq_bot := data.join_twoCore_eq_bot }

end Stellmacher
