module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.ReciprocalCoordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.AmbientSmallActor
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalLargeActor

/-!
# Exact critical indices in the original symplectic comparison

Both original endpoint covers give faithful ambient natural actions with
literal seed-centralizer kernels. Reciprocal moving indices exclude ambient
order two, after which both critical images are inner. A below-sixteen image
then forces both original critical indices to be four. In particular every
critical index is at least four, excluding the source's index-two case.

The failed-comparison wrapper obtains the below-sixteen bound from the
large-actor theorem. It retains only the original source hypotheses and the
separately produced inner-plane centralizer identities for the auxiliary Y.
No cover, actor marking, quotient kernel, or inner critical image is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)--(3.4), printed pp.867--868.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

theorem original_small_critical_indices_eq_four
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
    (hsmall : (Q R z).relIndex (Z R a) < 16) :
    (Q R z).relIndex (Z R a)=4 ∧ (Q R a).relIndex (Z R z)=4 := by
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨Fe,hFe,ee,hee,je,hje,hjre,κe,hκe,hκeQ,hκeC,hκeL,hψe,hconje,hproje,hkere⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore
      hc hC hsq path.end_color
  obtain ⟨Fa,hFa,ea,hea,ja,hja,hjra,κa,hκa,hκaQ,hκaC,hκaL,hψa,hconja,hproja,hkera⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore
      hc hC hsq path.start_color
  have hFec : Nat.card Fe.Carrier = 4 := by rw [Fe.card_eq,hFe]; norm_num
  have hFac : Nat.card Fa.Carrier = 4 := by rw [Fa.card_eq,hFa]; norm_num
  have hAZ : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hZA : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  let δe : Z R a →* J := κe.comp (inclusion hAZ)
  let δa : Z R z →* J := κa.comp (inclusion hZA)
  have hδecard : Nat.card δe.range = (Q R z).relIndex (Z R a) :=
    quotient_image_card _ _ _ hAZ κe hκeQ
  have hδacard : Nat.card δa.range = (Q R a).relIndex (Z R z) :=
    quotient_image_card _ _ _ hZA κa hκaQ
  have hδek := restricted_kernel_of_mapped_centralizer (Z R a) (stabilizer R z)
    (Z R z) hAZ κe hκeC
  have hδak := restricted_kernel_of_mapped_centralizer (Z R z) (stabilizer R a)
    (Z R a) hZA κa hκaC
  have hδe : ∀ x : Z R a, ∀ v : s.space.toSubmodule,
      je (Multiplicative.ofAdd (s.space.toRepresentation (δe x) v)) =
        (x : FreeAmalgam R) * je (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹ :=
    fun x v => hconje (inclusion hAZ x) v
  have hδa : ∀ x : Z R z, ∀ v : s.space.toSubmodule,
      ja (Multiplicative.ofAdd (s.space.toRepresentation (δa x) v)) =
        (x : FreeAmalgam R) * ja (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹ :=
    fun x v => hconja (inclusion hZA x) v
  obtain ⟨πe,hπes,hπe,hπea⟩ := exists_equivariant_embedded_projection
    (U R z) (Z R a) (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_actor_normalizes_moving path)
    s.space.toRepresentation (MovedSection.ambientAction s ee) je hje hjre
    (MovedSection.coverProjection s ee).toLinearMap hee.1
    (MovedSection.coverProjection_ambient s ee) δe hδe
  obtain ⟨πa,hπas,hπa,hπaa⟩ := exists_equivariant_embedded_projection
    (U R a) (Z R z) (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_reverse_actor_normalizes_moving path)
    s.space.toRepresentation (MovedSection.ambientAction s ea) ja hja hjra
    (MovedSection.coverProjection s ea).toLinearMap hea.1
    (MovedSection.coverProjection_ambient s ea) δa hδa
  have hedge := MSCentralOrbit.edgeCentralizerCondition R hp hQR hfaith
  obtain ⟨he4,ha4⟩ := CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_ambient_actor_orders_ge_four
    path hb hedge hFec hFac πe hπes πa hπas
    (MovedSection.ambientAction s ee) hψe (ambient_marking_semilinear hFec s ee)
    (MovedSection.ambientAction s ea) hψa (ambient_marking_semilinear hFac s ea)
    δe δa hδek hδak hπea hπaa
  let rev : CriticalPath R geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R geometry hedge a path.start_color
        (by rwa [geometry.distance_constant a path.start_color]) z path.end_color path.critical }
  obtain ⟨βe,hβec,hβem,hβe⟩ := critical_inner_model_actor path hb hFec s ee hee hC
    je hje hjre δe hδe (by omega)
  obtain ⟨βa,hβac,hβam,hβa⟩ := critical_inner_model_actor rev hb hFac s ea hea hC
    ja hja hjra δa hδa (by omega)
  let αe : Z R a →* Theory.SpecificGroups.SymplecticFour.Sp Fe.Carrier :=
    (commutator (Theory.SpecificGroups.SymplecticFour.Sp Fe.Carrier)).subtype.comp βe
  let αa : Z R z →* Theory.SpecificGroups.SymplecticFour.Sp Fa.Carrier :=
    (commutator (Theory.SpecificGroups.SymplecticFour.Sp Fa.Carrier)).subtype.comp βa
  have hαek : αe.ker=δe.ker := inner_model_kernel_eq s ee δe βe hβem
  have hαak : αa.ker=δa.ker := inner_model_kernel_eq s ea δa βa hβam
  have hαec : Nat.card αe.range=Nat.card δe.range := by rw [←index_ker,←index_ker,hαek]
  have hαac : Nat.card αa.range=Nat.card δa.range := by rw [←index_ker,←index_ker,hαak]
  have hacte : ∀ (x : Z R a) (u : U R z),
      πe ⟨x.val*u.val*x.val⁻¹,
        (mem_normalizer_iff.mp (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_actor_normalizes_moving path x.property)
          u.val).mp u.property⟩ = Multiplicative.ofAdd (αe x • (πe u).toAdd) := by
    intro x u
    rw [hπea,ambient_marking_inner_apply s ee δe βe hβem]
    rfl
  have hacta : ∀ (x : Z R z) (u : U R a),
      πa ⟨x.val*u.val*x.val⁻¹,
        (mem_normalizer_iff.mp (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_reverse_actor_normalizes_moving path x.property)
          u.val).mp u.property⟩ = Multiplicative.ofAdd (αa x • (πa u).toAdd) := by
    intro x u
    rw [hπaa,ambient_marking_inner_apply s ea δa βa hβam]
    rfl
  have hh := CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_small_inner_actor_card_four_of_fields
    path hb hedge hFec hFac πe hπes πa hπas αe αa
    (hαek.trans hδek) (hαak.trans hδak) hacte hacta (by rwa [hαec,hδecard])
  exact ⟨by rw [←hδecard,←hαec]; exact hh.1,
    by rw [←hδacard,←hαac]; exact hh.2.1⟩

theorem original_critical_indices_ge_four
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
    : 4 ≤ (Q R z).relIndex (Z R a) ∧ 4 ≤ (Q R a).relIndex (Z R z) := by
  by_cases he : (Q R z).relIndex (Z R a) < 16
  · obtain ⟨he,ha⟩ := original_small_critical_indices_eq_four R hms hp hne hQR hself hfaith
      q hq hcore hc hC hsq path hb he
    exact ⟨he.ge,ha.ge⟩
  by_cases ha : (Q R a).relIndex (Z R z) < 16
  · have hedge := MSCentralOrbit.edgeCentralizerCondition R hp hQR hfaith
    let rev : CriticalPath R geometry z a :=
      { start_color := path.end_color
        walk := path.walk.reverse
        shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
        critical := critical_reverse R geometry hedge a path.start_color
          (by rwa [geometry.distance_constant a path.start_color]) z path.end_color path.critical }
    obtain ⟨ha,he⟩ := original_small_critical_indices_eq_four R hms hp hne hQR hself hfaith
      q hq hcore hc hC hsq rev hb ha
    exact ⟨he.ge,ha.ge⟩
  exact ⟨by omega,by omega⟩

theorem original_critical_indices_eq_four_of_bad_comparison
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
    (hinner : Y ≤ Ltilde R z ⊔ centralizer (Z R z : Set (FreeAmalgam R)))
    (hcomm : ⁅Z R a,Y⁆ ≤ centralizer (Z R z : Set (FreeAmalgam R)))
    (hcentral : Y ≤ centralizer ((⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set _))
    (hbad : ¬ ⁅Z R z,Y⁆ ≤ ⁅X R a,X R z⁆ ⊔ ⁅X R a ⊓ Q R z,Y⁆) :
    (Q R z).relIndex (Z R a)=4 ∧ (Q R a).relIndex (Z R z)=4 := by
  apply original_small_critical_indices_eq_four R hms hp hne hQR hself hfaith q hq hcore
    hc hC hsq path hb
  exact original_large_critical_index_lt_sixteen R hms hp hne hQR hself hfaith q hq hcore
    hc hC hsq path hb Y hinner hcomm hcentral hbad

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
