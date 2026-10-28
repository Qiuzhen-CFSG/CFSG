module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.Comparison.CriticalImage.Model
public import Theory.GroupTheory.PrimeRankFixedJoin
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.Comparison.CriticalImage.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.Reduction

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# A common auxiliary subgroup on each G₂ critical edge

Every natural G₂ offender has the full elementary rank three. A central
involution c of the actual edge image therefore belongs to every offender
in that image. Take the commutator of its full actor preimage with the
starting seed. The exact actor kernel centralizes the seed, so this subgroup
lies in every critical commutator through the edge, without a quotient error.

It is normal in the edge kernel. If it were normal in the vertex stabilizer,
the opposite elementary seed and conjugate generation would make the entire
vertex residual centralize it. Its natural image would vanish, contradicting
the faithful nontrivial action of c. This constructs the literal witness in
MS93 (2.3)(d) directly; it does not identify the edge kernel with the parabolic
core or claim the witness is the printed C_U(Q₂).

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*,
(2.3)(d), (3.2)(vii), and (3.8), printed pp.857,863,877–878.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo
open Comparison.CriticalImage

private theorem offender_card (A : Subgroup (Atlas.G2.Model (ZMod 2)))
    (hA : IsOffender rho A) : Nat.card A = 2 ^ 3 := by
  obtain ⟨g,rfl⟩ := Atlas.G2.NaturalOffenders.offender_conjugate_elementary
    (F := ZMod 2) (n := 1) (by norm_num) (by decide) A hA
  rw [card_map_of_injective (MulAut.conj g).injective,
    Atlas.G2.EvenTwoRank.elementary_card, Nat.card_zmod]

/-- A central involution of a two-group containing natural offenders belongs
    to every one of them, since each already has the full elementary rank. -/
theorem common_edge_involution (B : Subgroup (Atlas.G2.Model (ZMod 2)))
    (hB : IsPGroup 2 B)
    (hE : ∃ E ≤ B, IsOffender rho E) :
    ∃ c ∈ B, orderOf c = 2 ∧ c ∈ centralizer (B : Set (Atlas.G2.Model (ZMod 2))) ∧
      ∀ E ≤ B, IsOffender rho E → c ∈ E := by
  obtain ⟨E,hEB,hE⟩ := hE
  have hBne : B ≠ ⊥ := by
    intro hz
    have hEz : E = ⊥ := bot_unique (hz ▸ hEB)
    have hc := offender_card E hE
    rw [hEz,card_bot] at hc
    norm_num at hc
  let : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).mpr hBne
  let : Nontrivial (center B) := hB.center_nontrivial
  have hp : IsPGroup 2 (center B) := hB.to_subgroup _
  obtain ⟨n,hn,hcard⟩ := hp.nontrivial_iff_card.mp inferInstance
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' (G := center B) 2
    (by rw [hcard]; exact dvd_pow_self 2 (by omega))
  have hcB : orderOf c.val = 2 :=
    (orderOf_injective (center B).subtype (center B).subtype_injective c).trans hc
  have hcG : orderOf c.val.val = 2 :=
    (orderOf_injective B.subtype B.subtype_injective c.val).trans hcB
  have hcent : c.val.val ∈ centralizer (B : Set (Atlas.G2.Model (ZMod 2))) := by
    intro b hb
    exact congrArg Subtype.val (mem_center_iff.mp c.property ⟨b,hb⟩)
  refine ⟨c.val.val,c.val.property,hcG,hcent,?_⟩
  intro A hAB hA
  by_contra hout
  let : IsElementaryAbelian 2 A := hA.1.2
  have hfix : A ≤ centralizer ({c.val.val} : Set (Atlas.G2.Model (ZMod 2))) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hcent a (hAB ha))
  have hb := IsElementaryAbelian.primeRank_ge_of_fixed_join A c.val.val hcG hout hfix
    (offender_card A hA)
  have hr := Atlas.G2.EvenTwoRank.two_rank (ZMod 2) (n := 1) (by norm_num)
  norm_num at hr
  omega
end CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo

open Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo
open ChapterC BinaryMS.MS93 BinaryMS.MS93.NormalizerTransfer Comparison Comparison.CriticalImage
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => R.subgroupOf (L ⊔ R)
variable (h : Pair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)))

include h in
private theorem edge_isPGroup {a t : Vertex T} (ha : color T a = false)
    (hat : Adjacent T a t) : IsPGroup 2 (Q T t) := by
  obtain ⟨f,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adjacent_iff_exists_common T a t).mp hat
  · have hh := Q_act T f (beta T)
    simp only [beta,act_hVertex,one_mul] at hh
    rw [hh,show Q T (hVertex T 1) = (T).map (embedM T) from Q_beta T]
    exact ((edge_two_group h).map _).map _
  · cases ha

include e in
private theorem critical_seed_le_first_edge (a : Vertex T) (ha : color T a = false)
    (z : Vertex T) (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t : Vertex T) (ht : (cosetGraph T).dist t z + 1 = (geometry h).b T) :
    Z T z ≤ Q T t := by
  have hz := critical_endpoint_color T a ha _ hc
  have hbz : 0 < criticalDistance T z ((geometry h).exists_critical z hz) := by
    rw [(geometry h).distance_constant z hz]
    exact (positive_even h e).1
  apply ((geometry h).omega_bound z hz hbz).trans
  apply X_le_Q_of_dist_lt T (geometry h) (edgeCentralizer h e) z hz t
  rw [SimpleGraph.dist_comm, (geometry h).distance_constant z hz]
  change _ < (geometry h).b T
  omega

include h e in
/-- A subgroup of a critical commutator that is normal at the starting vertex
is fixed by its residual. This is the obstruction to vertex normality used below. -/
private theorem normal_critical_subgroup_le_kernel
    (a : Vertex T) (ha : color T a = false) (z : Vertex T)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (ht : (cosetGraph T).dist t z + 1 = (geometry h).b T)
    (d : EndpointModel T a) (A : Subgroup (FreeAmalgam T))
    (hAD : A ≤ ⁅Z T a,Z T z⁆)
    (hn : (A.subgroupOf (stabilizer T a)).Normal) :
    A ≤ d.projection.ker.map (Z T a).subtype := by
  let S := stabilizer T a
  have hAZ := hAD.trans (critical_image_le_start (geometry h) a z ha hc)
  have hAS := hAZ.trans (Z_le_stabilizer T a)
  have hAe := hAD.trans (critical_image_le_endpoint (geometry h) a z ha hc)
  have hz := critical_endpoint_color T a ha _ hc
  have hp := (positive_even h e).1
  have hbz : 0 < criticalDistance T z ((geometry h).exists_critical z hz) := by
    rw [(geometry h).distance_constant z hz]; exact hp
  let := Z_elementary_of_positive T (geometry h) z hz hbz
  let C := S ⊓ centralizer (A : Set (FreeAmalgam T))
  have hCn : (C.subgroupOf S).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hg),
      mem_normalizer_iff_map_conj_eq.mp
        ((((normal_subgroupOf_iff_le_normalizer hAS).mp hn).trans
          (normalizer_le_normalizer_centralizer A)) hg)]
  have hZT := critical_seed_le_first_edge h e a ha z hc t ht
  have hTS := CriticalCriterion.edge_le_stabilizer T ha hat
  have hZC : Z T z ≤ C := by
    refine le_inf (hZT.trans hTS) ?_
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hAe hy⟩ : Z T z) ⟨x,hx⟩)
  have hba : 0 < criticalDistance T a ((geometry h).exists_critical a ha) := by
    rw [(geometry h).distance_constant a ha]; exact hp
  have hrev := critical_reverse T (geometry h) (edgeCentralizer h e) a ha hba z hz hc
  have hgen := CriticalCriterion.Generation.of_subgroup T (generation h e) ha hat hZT hrev.2
  have hspan : conjugatesIn (Z T z) S ≤ C := by
    apply iSup_le
    intro g
    exact (map_mono hZC).trans
      (mem_normalizer_iff_map_conj_eq.mp
        (((normal_subgroupOf_iff_le_normalizer inf_le_left).mp hCn)
          (S.inv_mem g.property))).le
  have hgenC : C ⊔ Q T t = S := le_antisymm (sup_le inf_le_left hTS)
    (hgen.ge.trans (sup_le_sup hspan le_rfl))
  let N := C.subgroupOf S
  let E := (Q T t).subgroupOf S
  let : N.Normal := hCn
  have htop : N ⊔ E = ⊤ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show C ≤ S from inf_le_left),
      map_subgroupOf_eq_of_le hTS, ← MonoidHom.range_eq_map, range_subtype]
    exact hgenC
  have hr : pResidual 2 S ≤ N := sInf_le
    ⟨inferInstance,isPGroup_quotient_of_sup_eq_top N E
      (edge_isPGroup h ha hat).comap_subtype htop⟩
  have hLC : Ltilde T a ≤ C := by
    have hh := map_mono (f := S.subtype) hr
    rwa [map_subgroupOf_eq_of_le (show C ≤ S from inf_le_left)] at hh
  rw [d.projection_kernel]
  exact le_inf hAZ (le_centralizer_iff.mp (hLC.trans inf_le_right))

private def actorLift {a : Vertex T} (d : EndpointModel T a)
    (c : Atlas.G2.Model (ZMod 2)) : Subgroup (FreeAmalgam T) :=
  ((zpowers c).comap d.actor).map (stabilizer T a).subtype

private theorem actorLift_normalized {a t : Vertex T} (ha : color T a = false)
    (hat : Adjacent T a t) (d : EndpointModel T a)
    (c : Atlas.G2.Model (ZMod 2))
    (hc : c ∈ centralizer (image d (Q T t) : Set (Atlas.G2.Model (ZMod 2)))) :
    Q T t ≤ normalizer (actorLift d c) := by
  have hS := CriticalCriterion.edge_le_stabilizer T ha hat
  have hn : (Q T t).subgroupOf (stabilizer T a) ≤
      normalizer ((zpowers c).comap d.actor) := by
    apply le_trans _ (le_normalizer_comap _)
    intro g hg
    apply centralizer_le_normalizer (zpowers c)
    rw [zpowers_eq_closure,centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr (hc (d.actor g) ⟨g,hg,rfl⟩)
  have hh := (map_mono (f := (stabilizer T a).subtype) hn).trans (le_normalizer_map _)
  rwa [map_subgroupOf_eq_of_le hS] at hh

include h e in
private theorem actorLift_commutator_le {a z : Vertex T} (ha : color T a = false)
    (_hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (d : EndpointModel T a) (c : Atlas.G2.Model (ZMod 2))
    (hcmem : c ∈ image d (Z T z)) :
    ⁅actorLift d c,Z T a⁆ ≤ ⁅Z T a,Z T z⁆ := by
  have hb := (positive_even h e).1
  have hba : 0 < criticalDistance T a ((geometry h).exists_critical a ha) := by
    rw [(geometry h).distance_constant a ha]; exact hb
  have hB : zpowers c ≤ image d (Z T z) := zpowers_le.mpr hcmem
  apply commutator_le.mpr
  intro y hy v hv
  obtain ⟨y',hy',rfl⟩ := hy
  obtain ⟨x,hx,hxy⟩ := hB hy'
  have hker : x⁻¹*y' ∈ d.actor.ker := by
    change d.actor (x⁻¹*y') = 1
    rw [map_mul,map_inv,hxy,inv_mul_cancel]
  have hQ : x.val⁻¹*y'.val ∈ Q T a := by
    rw [←d.actor_kernel]
    exact ⟨x⁻¹*y',hker,rfl⟩
  have hvq := Q_le_centralizer_X T a hQ v ((geometry h).omega_bound a ha hba hv)
  have heq : y'.val*v*y'.val⁻¹ = x.val*v*x.val⁻¹ := by
    have hh := congrArg (fun k => x.val*k*y'.val⁻¹) hvq.symm
    simpa [mul_assoc] using hh
  change y'.val*v*y'.val⁻¹*v⁻¹ ∈ ⁅Z T a,Z T z⁆
  rw [heq, commutator_comm]
  exact commutator_mem_commutator hx hv

omit [Finite G] in
private theorem actorLift_moves {a : Vertex T} (d : EndpointModel T a)
    (c : Atlas.G2.Model (ZMod 2)) (hc : c ≠ 1) (hcr : c ∈ d.actor.range) :
    ¬ ⁅actorLift d c,Z T a⁆ ≤ d.projection.ker.map (Z T a).subtype := by
  intro hle
  obtain ⟨y,hy⟩ := hcr
  have hyL : y.val ∈ actorLift d c := ⟨y,by change d.actor y ∈ zpowers c; rw [hy]; exact mem_zpowers c,rfl⟩
  have hfix (v : Z T a) : rho c (d.projection v).toAdd = (d.projection v).toAdd := by
    have hw := hle (commutator_mem_commutator hyL v.property)
    obtain ⟨w,hw,hwe⟩ := hw
    have hconj : (⟨y.val*v.val*y.val⁻¹,
        (mem_normalizer_iff.mp (Z_normalized T a y.property) v.val).mp v.property⟩ : Z T a) = w*v := by
      apply Subtype.ext
      change y.val*v.val*y.val⁻¹ = w.val*v.val
      change w.val = ⁅y.val,v.val⁆ at hwe
      rw [hwe]
      simp [commutatorElement_def,mul_assoc]
    have hh := d.intertwines y v
    rw [hconj,map_mul,show d.projection w = 1 from hw,one_mul,hy] at hh
    exact (congrArg Multiplicative.toAdd hh).symm
  have hρ : rho c = rho 1 := by
    apply LinearMap.ext
    intro v
    obtain ⟨w,hw⟩ := d.projection_surjective (Multiplicative.ofAdd v)
    simpa only [hw,toAdd_ofAdd,map_one,Module.End.one_apply] using hfix w
  apply hc
  apply Atlas.G2.Natural.action_injective (ZMod 2)
  exact (LinearEquiv.conjAlgEquiv (ZMod 2)
    (Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2))).injective hρ

include h e in
/-- The edge witness uses a common central involution of the actual edge image.
Its commutator is contained in every critical commutator through that edge. -/
theorem edgeWitness_knownSimple
    (a : Vertex T) (ha : color T a = false) (z : Vertex T)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (ht : (cosetGraph T).dist t z + 1 = (cosetGraph T).dist a z) :
    ∃ A, CriticalCriterion.EdgeWitness T (geometry h) a t A := by
  let g := geometry h
  have hpos := (positive_even h e).1
  have hba : 0 < criticalDistance T a (g.exists_critical a ha) := by
    rw [g.distance_constant a ha]; exact hpos
  have ht' : (cosetGraph T).dist t z + 1 = g.b T :=
    ht.trans (hc.1.trans (g.distance_constant a ha))
  obtain ⟨d⟩ := endpointModel_knownSimple h e ha
  have hcrit (w : Vertex T) (hw : CriticalPair T a w (g.exists_critical a ha))
      (htw : (cosetGraph T).dist t w + 1 = g.b T) :
      image d (Z T w) ≤ image d (Q T t) ∧ IsOffender rho (image d (Z T w)) := by
    have hwc := critical_endpoint_color T a ha _ hw
    have hbw : 0 < criticalDistance T w (g.exists_critical w hwc) := by
      rw [g.distance_constant w hwc]; exact hpos
    have hrev := critical_reverse T g (edgeCentralizer h e) a ha hba w hwc hw
    obtain ⟨dw⟩ := endpointModel_knownSimple h e hwc
    exact ⟨map_mono (comap_mono (critical_seed_le_first_edge h e a ha w hw t htw)),
      critical_image_offender g (edgeCentralizer h e) w a hwc hpos hrev dw d⟩
  obtain ⟨c,hcB,hc2,hcC,hcommon⟩ := common_edge_involution (image d (Q T t))
    (((edge_isPGroup h ha hat).comap_subtype).map d.actor)
    ⟨image d (Z T z),(hcrit z hc ht').1,(hcrit z hc ht').2⟩
  let A := ⁅actorLift d c,Z T a⁆
  have hbound (w : Vertex T) (hw : CriticalPair T a w (g.exists_critical a ha))
      (htw : (cosetGraph T).dist t w + 1 = g.b T) : A ≤ ⁅Z T a,Z T w⁆ :=
    actorLift_commutator_le h e ha hw d c
      (hcommon _ (hcrit w hw htw).1 (hcrit w hw htw).2)
  have hAZ : A ≤ Z T a := (hbound z hc ht').trans (critical_image_le_start g a z ha hc)
  refine ⟨A,⟨hAZ.trans (g.omega_bound a ha hba),?_,?_,?_⟩⟩
  · apply normal_subgroupOf_of_le_normalizer
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (actorLift_normalized ha hat d c hcC hx),
      mem_normalizer_iff_map_conj_eq.mp
        (Z_normalized T a (CriticalCriterion.edge_le_stabilizer T ha hat hx))]
  · intro hn
    apply actorLift_moves d c (by intro hc1; rw [hc1,orderOf_one] at hc2; omega) _
      (normal_critical_subgroup_le_kernel h e a ha z hc t hat ht' d A (hbound z hc ht') hn)
    obtain ⟨x,hx,hxc⟩ := hcB
    exact ⟨x,hxc⟩
  · intro ha' w hw htw
    have hwc := critical_endpoint_color T a ha _ hw
    have hbw : 0 < criticalDistance T w (g.exists_critical w hwc) := by
      rw [g.distance_constant w hwc]; exact hpos
    exact (hbound w hw htw).trans
      (commutator_mono (g.omega_bound a ha hba) (g.omega_bound w hwc hbw))

end CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo
