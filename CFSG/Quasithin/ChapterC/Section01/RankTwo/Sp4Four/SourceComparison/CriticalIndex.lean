module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSmallActor
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.InnerPlaneActors

/-!
# Exact order four from the original failed comparison

The adjacent-core actor centralizes the actual critical commutator. In the
large-image branch this supplies the inner-plane conditions and forces the
critical index below sixteen. The reciprocal small-image theorem then makes
both original critical indices four. All cover, marking, field-twist, plane,
and original-centralizer transport inputs are discharged internally.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii)(2), printed p.867,
cardinality conclusion. The X-decomposition and later iterated-commutator
conclusion are separate source branches.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

theorem original_critical_indices_eq_four_of_local_actor
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R))
    (hYZ : Y ≤ stabilizer R z)
    (hcentral : Y ≤ centralizer ((⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set _))
    (hbad : ¬ ⁅Z R z,Y⁆ ≤ ⁅X R a,X R z⁆ ⊔ ⁅X R a ⊓ Q R z,Y⁆) :
    (Q R z).relIndex (Z R a)=4 ∧ (Q R a).relIndex (Z R z)=4 := by
  apply original_small_critical_indices_eq_four R hms hp hne hQR hself hfaith q hq hcore
    hc hC hsq path hb
  exact original_large_critical_index_lt_sixteen_of_local_actor R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb Y hYZ hcentral hbad

theorem original_critical_indices_eq_four_of_adjacent_core
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R))
    {t : Vertex R} (ht : Adjacent R z t) (hYQ : Y ≤ Q R t)
    (hcentral : Y ≤ centralizer ((⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set _))
    (hbad : ¬ ⁅Z R z,Y⁆ ≤ ⁅X R a,X R z⁆ ⊔ ⁅X R a ⊓ Q R z,Y⁆) :
    (Q R z).relIndex (Z R a)=4 ∧ (Q R a).relIndex (Z R z)=4 := by
  apply original_small_critical_indices_eq_four R hms hp hne hQR hself hfaith q hq hcore
    hc hC hsq path hb
  exact original_large_critical_index_lt_sixteen_of_adjacent_core R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb Y ht hYQ hcentral hbad

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
