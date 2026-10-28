module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.DistanceFour.DerivedMidpoint
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.Midpoint
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.DistanceFour.Radius
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.LocalControl.Auxiliary

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# The G₂ critical commutator on its first edge

The whole radius image at an endpoint has order at most eight and contains
its opposite critical seed image of order eight. Equality, with the exact
actor kernel, identifies the critical commutator with the starting seed's
commutator with the whole midpoint radius. Both factors are normalized by
the first edge kernel, so this critical commutator is normalized there.

The derived radius lies in every incident elementary edge radius, hence
centralizes the whole radius. In particular the source triple commutator
stays inside the critical commutator and centralizes the midpoint radius.
If that triple commutator vanishes, the whole critical commutator becomes
a common edge witness. Source (2.3) then makes it residual-fixed at the
midpoint. The vanishing itself is not asserted here.

The two private imports reuse the earlier endpoint fixed-space cardinality,
critical-seed edge containment, and critical-subgroup normality obstruction.
No private declaration occurs in the public statements.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
(2.3) and (3.8), printed pp.857--859,878--879. The natural coordinates retain
the ATLAS attribution in LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour
open ChapterC BinaryMS.MS93 BinaryMS.MS93.NaturalStructure.Exclusion
open Comparison Comparison.CriticalImage
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => R.subgroupOf (L ⊔ R)
variable (h : Pair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)))
include h e

/-- The whole derived radius is central in the radius. -/
theorem radius_derived_centralizes_radius
    (hb : (geometry h).b T = 4) (a : Vertex T) (ha : color T a = false) :
    ⁅V T a,V T a⁆ ≤ centralizer (V T a : Set (FreeAmalgam T)) := by
  apply le_centralizer_iff.mpr
  apply radius_le_of_m_ball ha
  intro d hd hda
  obtain ⟨t,hat,hdt⟩ : ∃ t, Adjacent T a t ∧
      Z T d ≤ V T t := by
    by_cases he : d = a
    · subst d
      obtain ⟨z,hcrit⟩ := criticalPair_exists T a ((geometry h).exists_critical a ha)
      obtain ⟨t,hat,_⟩ := exists_adjacent_dist_sub_one T a z (by
        rw [hcrit.1,(geometry h).distance_constant a ha]
        exact (positive_even h e).1)
      refine ⟨t,hat,le_iSup_of_le a (le_iSup_of_le ?_ le_rfl)⟩
      exact (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr hat)).le.trans
        (by decide)
    · have htwo : (cosetGraph T).dist a d = 2 := by
        have hn : (cosetGraph T).dist a d ≠ 0 := by
          intro hz
          exact he ((cosetGraph_connected T).dist_eq_zero_iff.mp hz).symm
        have heven : Even ((cosetGraph T).dist a d) := by
          obtain ⟨w,hw⟩ := (cosetGraph_connected T).exists_walk_length_eq_dist a d
          rw [←hw,walk_even_iff_color_eq,ha,hd]
        rw [Nat.even_iff] at heven
        rw [SimpleGraph.dist_comm] at hda
        omega
      obtain ⟨t,hat,hdt⟩ := exists_common_neighbor_of_dist_two T a d htwo
      refine ⟨t,hat,le_iSup_of_le d (le_iSup_of_le ?_ le_rfl)⟩
      exact (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr hdt)).le.trans
        (by decide)
  exact hdt.trans ((le_centralizer_iff_isMulCommutative.mpr
    (edge_radius_commutative (geometry h) (by omega) a t ha hat)).trans
      (centralizer_le (radius_derived_le_edge h e hb a t ha hat)))

/-- At a critical midpoint the whole radius has the same endpoint actor
image as the opposite seed. -/
theorem critical_radius_image_eq
    (hb : (geometry h).b T = 4)
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (c : Vertex T) (hcColor : color T c = false)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2)
    (d : EndpointModel T a) : image d (V T c) = image d (Z T z) := by
  have hz := critical_endpoint_color T a ha _ hc
  have hrev := critical_reverse T (geometry h) (edgeCentralizer h e) a ha (by
    rw [(geometry h).distance_constant a ha]; exact (positive_even h e).1) z hz hc
  have hZV : Z T z ≤ V T c := le_iSup_of_le z (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm,hcz]) le_rfl)
  have hle : image d (Z T z) ≤ image d (V T c) := map_mono (comap_mono hZV)
  have hcard := critical_image_card_eight h e z a hz hrev d
  have hE := radius_image_elementary_at_distance_four h e hb c a hcColor ha
    (by rw [SimpleGraph.dist_comm,hac]) d
  have hr := Atlas.G2.EvenTwoRank.two_rank (ZMod 2) (n := 1) (by norm_num)
  have hbound := (primeRank_le_iff_elementary_card_le (Atlas.G2.Model (ZMod 2))).mp
    hr.le (image d (V T c)) hE
  exact (eq_of_le_of_card_ge hle (by simpa [hcard] using hbound)).symm

/-- The critical commutator is the full commutator of the starting seed
with the midpoint radius, with no fixed-kernel error. -/
theorem critical_commutator_eq_radius
    (hb : (geometry h).b T = 4)
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (c : Vertex T) (hcColor : color T c = false)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2) :
    ⁅Z T a,Z T z⁆ = ⁅Z T a,V T c⁆ := by
  obtain ⟨d⟩ := endpointModel_knownSimple h e ha
  have he := critical_radius_image_eq h e hb a z ha hc c hcColor hac hcz d
  have hVS : V T c ≤ stabilizer T a :=
    ((geometry h).V_le_Q (by omega) c hcColor).trans
      (Q_le_stabilizer_of_dist_two T c a hcColor (by rw [SimpleGraph.dist_comm,hac]))
  have hZV : Z T z ≤ V T c := le_iSup_of_le z (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm,hcz]) le_rfl)
  apply le_antisymm (commutator_mono le_rfl hZV)
  rw [commutator_comm]
  apply commutator_le.mpr
  intro v hv x hx
  let v' : stabilizer T a := ⟨v,hVS hv⟩
  have hm : d.actor v' ∈ image d (Z T z) := he ▸ mem_map_of_mem d.actor hv
  obtain ⟨w,hw,hwv⟩ := hm
  have hk : w⁻¹*v' ∈ d.actor.ker := by
    change d.actor (w⁻¹*v') = 1
    rw [map_mul,map_inv,hwv,inv_mul_cancel]
  have hQ : w.val⁻¹*v ∈ Q T a := by
    rw [←d.actor_kernel]
    exact ⟨w⁻¹*v',hk,rfl⟩
  have hxq := Q_le_centralizer_X T a hQ x ((geometry h).omega_bound a ha (by
    rw [(geometry h).distance_constant a ha]; exact (positive_even h e).1) hx)
  have hconj : v*x*v⁻¹ = w.val*x*w.val⁻¹ := by
    have hh := congrArg (fun k => w.val*k*v⁻¹) hxq.symm
    simpa [mul_assoc] using hh
  change v*x*v⁻¹*x⁻¹ ∈ ⁅Z T a,Z T z⁆
  rw [hconj,commutator_comm]
  exact commutator_mem_commutator hw hx

/-- The critical commutator is normalized by the actual first edge kernel. -/
theorem critical_commutator_normalized_edge
    (hb : (geometry h).b T = 4)
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t c : Vertex T) (hcColor : color T c = false)
    (hat : Adjacent T a t) (hct : Adjacent T c t)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2) :
    Q T t ≤ normalizer (⁅Z T a,Z T z⁆ : Subgroup (FreeAmalgam T)) := by
  rw [critical_commutator_eq_radius h e hb a z ha hc c hcColor hac hcz]
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp
      (Z_normalized T a (CriticalCriterion.edge_le_stabilizer T ha hat hx)),
    mem_normalizer_iff_map_conj_eq.mp
      (V_normalized c (CriticalCriterion.edge_le_stabilizer T hcColor hct hx))]



/-- The source triple commutator stays inside the original critical
commutator and centralizes the whole midpoint radius. -/
theorem critical_triple_control
    (hb : (geometry h).b T = 4)
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t c : Vertex T) (hcColor : color T c = false)
    (hat : Adjacent T a t) (hct : Adjacent T c t)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2) :
    ⁅⁅Z T a,Z T z⁆,Q T t⁆ ≤ ⁅Z T a,Z T z⁆ ∧
      ⁅⁅Z T a,Z T z⁆,Q T t⁆ ≤ centralizer (V T c : Set (FreeAmalgam T)) := by
  have hle := le_normalizer_iff_commutator_le_left.mp
    (critical_commutator_normalized_edge h e hb a z ha hc t c hcColor hat hct hac hcz)
  have haV : Z T a ≤ V T c := le_iSup_of_le a (le_iSup_of_le hac.le le_rfl)
  have hzV : Z T z ≤ V T c := le_iSup_of_le z (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm,hcz]) le_rfl)
  exact ⟨hle,hle.trans ((commutator_mono haV hzV).trans
    (radius_derived_centralizes_radius h e hb c hcColor))⟩

/-- A critical commutator cannot be normal in its starting vertex group. -/
theorem critical_commutator_not_normal_vertex
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (ht : (cosetGraph T).dist t z + 1 = (geometry h).b T) :
    ¬ ((⁅Z T a,Z T z⁆).subgroupOf (stabilizer T a)).Normal := by
  intro hn
  obtain ⟨da⟩ := endpointModel_knownSimple h e ha
  have hz := critical_endpoint_color T a ha _ hc
  obtain ⟨dz⟩ := endpointModel_knownSimple h e hz
  have hkernel := normal_critical_subgroup_le_kernel h e a ha z hc t hat ht da
    ⁅Z T a,Z T z⁆ le_rfl hn
  have hrev := critical_reverse T (geometry h) (edgeCentralizer h e) a ha (by
    rw [(geometry h).distance_constant a ha]; exact (positive_even h e).1) z hz hc
  have hoff := critical_image_offender (geometry h) (edgeCentralizer h e)
    z a hz (positive_even h e).1 hrev dz da
  have hcover := critical_fixed_covered (geometry h) (edgeCentralizer h e)
    z a hz (positive_even h e).1 hrev dz da
  have hzero (w : fixedSpace rho (image da (Z T z))) : w = 0 := by
    obtain ⟨v,hv,hvw⟩ := hcover w w.property
    rw [commutator_comm] at hv
    obtain ⟨x,hx,hxv⟩ := hkernel hv
    have hxv' : x = v := Subtype.ext hxv
    have hvzero : da.projection v = 1 := hxv' ▸ hx
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (hvw.symm.trans hvzero)
  let : Subsingleton (fixedSpace rho (image da (Z T z))) :=
    ⟨fun v w => (hzero v).trans (hzero w).symm⟩
  have hbnd := Finite.card_le_one_iff_subsingleton.mpr
    (inferInstance : Subsingleton (fixedSpace rho (image da (Z T z))))
  rw [offender_fixed_card _ hoff] at hbnd
  omega

/-- Centralization by the first edge identifies its whole seed commutator
with the specified critical commutator. -/
theorem critical_commutator_eq_edge_of_centralizes
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (ht : (cosetGraph T).dist t z + 1 = (geometry h).b T)
    (hcentral : ⁅Z T a,Z T z⁆ ≤ centralizer (Q T t : Set (FreeAmalgam T))) :
    ⁅Z T a,Z T z⁆ = ⁅Z T a,Q T t⁆ := by
  have hz := critical_endpoint_color T a ha _ hc
  have hrev := critical_reverse T (geometry h) (edgeCentralizer h e) a ha (by
    rw [(geometry h).distance_constant a ha]; exact (positive_even h e).1) z hz hc
  obtain ⟨da⟩ := endpointModel_knownSimple h e ha
  obtain ⟨dz⟩ := endpointModel_knownSimple h e hz
  apply le_antisymm (commutator_mono le_rfl
    (critical_seed_le_first_edge h e a ha z hc t ht))
  rw [commutator_comm]
  have hc' : Q T t ≤ centralizer
      ((⁅Z T z,Z T a⁆ : Subgroup (FreeAmalgam T)) : Set (FreeAmalgam T)) := by
    rw [commutator_comm]
    exact le_centralizer_iff.mp hcentral
  have hh := critical_commutator_le (geometry h) (edgeCentralizer h e)
    z a hz (positive_even h e).1 hrev dz da (Q T t)
    (CriticalCriterion.edge_le_stabilizer T ha hat) hc'
  rwa [commutator_comm (Z T z) (Z T a)] at hh

/-- Once its triple commutator with the first edge vanishes, the whole
critical commutator is an admissible common auxiliary subgroup. -/
theorem critical_commutator_edgeWitness_of_centralizes
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (ht : (cosetGraph T).dist t z + 1 = (geometry h).b T)
    (hcentral : ⁅Z T a,Z T z⁆ ≤ centralizer (Q T t : Set (FreeAmalgam T))) :
    CriticalCriterion.EdgeWitness T (geometry h) a t ⁅Z T a,Z T z⁆ := by
  have hAZ : ⁅Z T a,Z T z⁆ ≤ Z T a :=
    critical_image_le_start (geometry h) a z ha hc
  have hba : 0 < criticalDistance T a ((geometry h).exists_critical a ha) := by
    rw [(geometry h).distance_constant a ha]; exact (positive_even h e).1
  refine ⟨hAZ.trans ((geometry h).omega_bound a ha hba),?_,
    critical_commutator_not_normal_vertex h e a z ha hc t hat ht,?_⟩
  · apply normal_subgroupOf_of_le_normalizer
    exact (le_centralizer_iff.mp hcentral).trans (Subgroup.centralizer_le_normalizer _)
  · intro ha' w hw htw
    have hD := critical_commutator_eq_edge_of_centralizes h e a z ha hc t hat ht hcentral
    have hwD : ⁅Z T a,Z T w⁆ ≤ ⁅Z T a,Z T z⁆ := by
      rw [hD]
      exact commutator_mono le_rfl (critical_seed_le_first_edge h e a ha' w hw t htw)
    have hwcentral := hwD.trans hcentral
    have hwedge := critical_commutator_eq_edge_of_centralizes h e a w ha' hw t hat htw hwcentral
    rw [hD,←hwedge]
    have hbw : 0 < criticalDistance T w
        ((geometry h).exists_critical w (critical_endpoint_color T a ha' _ hw)) := by
      rw [(geometry h).distance_constant w (critical_endpoint_color T a ha' _ hw)]
      exact (positive_even h e).1
    exact commutator_mono ((geometry h).omega_bound a ha hba)
      ((geometry h).omega_bound w (critical_endpoint_color T a ha' _ hw) hbw)

/-- Source (2.3) now fixes the entire critical commutator at its midpoint,
using exactly the vanishing triple commutator from the end of (3.8). -/
theorem critical_commutator_le_fixed_of_centralizes
    (hb : (geometry h).b T = 4)
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t c : Vertex T) (hcColor : color T c = false)
    (hat : Adjacent T a t) (hct : Adjacent T c t)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2)
    (hcentral : ⁅Z T a,Z T z⁆ ≤ centralizer (Q T t : Set (FreeAmalgam T))) :
    ⁅Z T a,Z T z⁆ ≤ fixedCore T c := by
  have hd : (cosetGraph T).dist a z = 4 :=
    hc.1.trans (((geometry h).distance_constant a ha).trans hb)
  have ht : (cosetGraph T).dist t z + 1 = (geometry h).b T := by
    have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr hat)
    have htc1 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj T _ _).mpr (adjacent_symm T hct))
    have h₁ := (cosetGraph_connected T).dist_triangle (u := a) (v := t) (w := z)
    have h₂ := (cosetGraph_connected T).dist_triangle (u := t) (v := c) (w := z)
    omega
  exact auxiliary_le_fixed_midpoint h e (by omega)
    (localControl_knownSimple G L R h e (by omega)) a ha z hc t c hcColor hat hct hac hcz
    _ (critical_commutator_edgeWitness_of_centralizes h e a z ha hc t hat ht hcentral)

end CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour

