module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.DistanceFour.LongRootModel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.DistanceFour.MidpointMovement
public import Theory.AtlasPort.LinearGroups.G2.BinarySecondParabolic
public import Theory.AtlasPort.LinearGroups.G2.LieSylowCenter
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.LocalControl.Auxiliary

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# The long-root auxiliary subgroup on the original critical edge

The actual edge-kernel image normalizes the critical radius image. Aligning
both images at once selects a highest long root central in the edge image.
Its full preimage under the original endpoint actor gives an auxiliary
commutator contained in every critical commutator through this edge.
The existing source (2.3) argument fixes it at the same midpoint.

The natural displacement calculation also places the literal critical
triple inside this auxiliary joined with the original projection kernel.
The kernel is retained: removing it requires the trace-zero covering model
of the moving seed, and remains part of the MS93 (3.8) assembly. No
NonfixedCriticalEdgeInput or unconditional reconstruction is asserted here.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*,
(2.3) and (3.8), printed pp.857–859 and 879. The private import reuses the
full-actor preimage and vertex-normality obstruction already proved in
LocalControl.Auxiliary. Root formulas retain LICENSES/ATLAS.txt attribution.
-/

open Subgroup Representation Representation.BinaryOffender
open Atlas.G2
@[expose] public noncomputable section

open Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour
open ChapterC BinaryMS.MS93 Comparison Comparison.CriticalImage
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => R.subgroupOf (L ⊔ R)
variable (h : Pair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)))

include h e in
theorem critical_edge_image_normalizes
    (hb : (geometry h).b T = 4)
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t c : Vertex T) (hcColor : color T c = false)
    (hct : Adjacent T c t)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2)
    (d : EndpointModel T a) :
    image d (Q T t) ≤ normalizer (image d (Z T z) : Set (Atlas.G2.Model (ZMod 2))) := by
  rw [←critical_radius_image_eq h e hb a z ha hc c hcColor hac hcz d]
  have hn : (Q T t).subgroupOf (stabilizer T a) ≤
      normalizer ((V T c).subgroupOf (stabilizer T a)) := by
    apply le_trans _ (le_normalizer_comap (stabilizer T a).subtype)
    intro x hx
    exact V_normalized c (CriticalCriterion.edge_le_stabilizer T hcColor hct hx)
  exact (map_mono hn).trans (le_normalizer_map d.actor)

private theorem central_involution_mem_offender
    (B E : Subgroup (Atlas.G2.Model (ZMod 2)))
    (c : Atlas.G2.Model (ZMod 2)) (hc2 : orderOf c = 2)
    (hc : c ∈ centralizer (B : Set (Atlas.G2.Model (ZMod 2))))
    (hEB : E ≤ B) (hE : IsOffender rho E) : c ∈ E := by
  by_contra hout
  let : IsElementaryAbelian 2 E := hE.1.2
  have hfix : E ≤ centralizer ({c} : Set (Atlas.G2.Model (ZMod 2))) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hc a (hEB ha))
  have hb := IsElementaryAbelian.primeRank_ge_of_fixed_join E c hc2 hout hfix
    (offender_card E hE)
  have hr := Atlas.G2.EvenTwoRank.two_rank (ZMod 2) (n := 1) (by norm_num)
  norm_num at hr
  omega

/-- The auxiliary retains the full preimage under the actual endpoint actor. -/
def rootAuxiliary {a : Vertex T} (d : EndpointModel T a)
    (g : Atlas.G2.Model (ZMod 2)) : Subgroup (FreeAmalgam T) :=
  ⁅((zpowers (MulAut.conj g (Atlas.G2.rootA 1))).comap d.actor).map
    (stabilizer T a).subtype,Z T a⁆

include h e in
theorem rootAuxiliary_edgeWitness
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (ht : (cosetGraph T).dist t z + 1 = (geometry h).b T)
    (d : EndpointModel T a) (g : Atlas.G2.Model (ZMod 2))
    (hE : image d (Z T z) = (Atlas.G2.EvenTwoRank.elementary (ZMod 2)).map
      (MulAut.conj g).toMonoidHom)
    (hB : image d (Q T t) ≤ Atlas.G2.unipotent.map (MulAut.conj g).toMonoidHom) :
    CriticalCriterion.EdgeWitness T (geometry h) a t (rootAuxiliary d g) := by
  let r := MulAut.conj g (Atlas.G2.rootA (1 : ZMod 2))
  have hr2 : orderOf r = 2 := by
    change orderOf ((MulAut.conj g).toMonoidHom (Atlas.G2.rootA (1 : ZMod 2))) = 2
    rw [orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective]
    apply orderOf_eq_prime
    · rw [pow_two,Atlas.G2.rootA_add,CharTwo.add_self_eq_zero,Atlas.G2.rootA_zero]
    · exact Atlas.G2.BinaryCore.z_ne_one
  have hrE : r ∈ image d (Z T z) := by
    rw [hE]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom
      (Atlas.G2.NaturalOffenders.rootA_mem_elementary 1)
  have hrB : r ∈ image d (Q T t) :=
    (map_mono (comap_mono (critical_seed_le_first_edge h e a ha z hc t ht))) hrE
  have hrC : r ∈ centralizer (image d (Q T t) : Set (Atlas.G2.Model (ZMod 2))) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hB hx
    rw [Atlas.G2.unipotent_eq_range] at hy
    obtain ⟨v,rfl⟩ := hy
    dsimp only [r]
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg (MulAut.conj g)
      (Atlas.G2.LieParabolicSetup.unipotentProduct_commute_rootA v 1).eq
  have hpos := (positive_even h e).1
  have hba : 0 < criticalDistance T a ((geometry h).exists_critical a ha) := by
    rw [(geometry h).distance_constant a ha]; exact hpos
  have hbound (w : Vertex T) (hw : CriticalPair T a w ((geometry h).exists_critical a ha))
      (htw : (cosetGraph T).dist t w + 1 = (geometry h).b T) :
      rootAuxiliary d g ≤ ⁅Z T a,Z T w⁆ := by
    have hwc := critical_endpoint_color T a ha _ hw
    have hrev := critical_reverse T (geometry h) (edgeCentralizer h e) a ha hba w hwc hw
    obtain ⟨dw⟩ := endpointModel_knownSimple h e hwc
    apply actorLift_commutator_le h e ha hw d r
    exact central_involution_mem_offender _ _ r hr2 hrC
      (map_mono (comap_mono (critical_seed_le_first_edge h e a ha w hw t htw)))
      (critical_image_offender (geometry h) (edgeCentralizer h e)
        w a hwc hpos hrev dw d)
  have hAZ : rootAuxiliary d g ≤ Z T a :=
    (hbound z hc ht).trans (critical_image_le_start (geometry h) a z ha hc)
  refine ⟨hAZ.trans ((geometry h).omega_bound a ha hba),?_,?_,?_⟩
  · apply normal_subgroupOf_of_le_normalizer
    intro x hx
    change x ∈ normalizer (⁅actorLift d r,Z T a⁆ : Subgroup (FreeAmalgam T))
    rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (actorLift_normalized ha hat d r hrC hx),
      mem_normalizer_iff_map_conj_eq.mp
        (Z_normalized T a (CriticalCriterion.edge_le_stabilizer T ha hat hx))]
  · intro hn
    apply actorLift_moves d r (by intro hr1; rw [hr1,orderOf_one] at hr2; omega) _
      (normal_critical_subgroup_le_kernel h e a ha z hc t hat ht d _ (hbound z hc ht) hn)
    obtain ⟨x,hx,hxr⟩ := hrB
    exact ⟨x,hxr⟩
  · intro ha' w hw htw
    have hwc := critical_endpoint_color T a ha _ hw
    have hbw : 0 < criticalDistance T w ((geometry h).exists_critical w hwc) := by
      rw [(geometry h).distance_constant w hwc]; exact hpos
    exact (hbound w hw htw).trans (commutator_mono
      ((geometry h).omega_bound a ha hba) ((geometry h).omega_bound w hwc hbw))

include h e in
theorem critical_edge_root_auxiliary
    (hb : (geometry h).b T = 4)
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t c : Vertex T) (hcColor : color T c = false)
    (hat : Adjacent T a t) (hct : Adjacent T c t)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2)
    (d : EndpointModel T a) :
    ∃ g : Atlas.G2.Model (ZMod 2),
      image d (Z T z) = (Atlas.G2.EvenTwoRank.elementary (ZMod 2)).map
        (MulAut.conj g).toMonoidHom ∧
      image d (Q T t) ≤ Atlas.G2.unipotent.map (MulAut.conj g).toMonoidHom ∧
      CriticalCriterion.EdgeWitness T (geometry h) a t (rootAuxiliary d g) ∧
      rootAuxiliary d g ≤ fixedCore T c := by
  have hz := critical_endpoint_color T a ha _ hc
  have hrev := critical_reverse T (geometry h) (edgeCentralizer h e) a ha (by
    rw [(geometry h).distance_constant a ha]; exact (positive_even h e).1) z hz hc
  obtain ⟨dz⟩ := endpointModel_knownSimple h e hz
  obtain ⟨g,hE,hB⟩ := CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour.LongRootModel.simultaneous_alignment
    (image d (Z T z)) (image d (Q T t))
    (critical_image_offender (geometry h) (edgeCentralizer h e)
      z a hz (positive_even h e).1 hrev dz d)
    (((edge_isPGroup h ha hat).comap_subtype).map d.actor)
    (critical_edge_image_normalizes h e hb a z ha hc t c hcColor hct hac hcz d)
  have ht : (cosetGraph T).dist t z + 1 = (geometry h).b T := by
    have hd : (cosetGraph T).dist a z = 4 :=
      hc.1.trans (((geometry h).distance_constant a ha).trans hb)
    have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr hat)
    have htc1 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj T _ _).mpr (adjacent_symm T hct))
    have h₁ := (cosetGraph_connected T).dist_triangle (u := a) (v := t) (w := z)
    have h₂ := (cosetGraph_connected T).dist_triangle (u := t) (v := c) (w := z)
    omega
  have hA := rootAuxiliary_edgeWitness h e a z ha hc t hat ht d g hE hB
  exact ⟨g,hE,hB,hA,auxiliary_le_fixed_midpoint h e (by omega)
    (localControl_knownSimple G L R h e (by omega)) a ha z hc t c hcColor hat hct hac hcz _ hA⟩

end CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour


open Subgroup Representation Representation.BinaryOffender
open Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour
open ChapterC BinaryMS.MS93 Comparison Comparison.CriticalImage
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => R.subgroupOf (L ⊔ R)
variable (h : Pair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)))

private def seedDisplacement {a : Vertex T} (s : stabilizer T a) (v : Z T a) : Z T a :=
  ⟨⁅s.val,v.val⁆,(Z T a).mul_mem
    ((mem_normalizer_iff.mp (Z_normalized T a s.property) v.val).mp v.property)
    ((Z T a).inv_mem v.property)⟩

omit [Finite G] in private theorem seedDisplacement_projection {a : Vertex T} (d : EndpointModel T a)
    (s : stabilizer T a) (v : Z T a) :
    d.projection (seedDisplacement s v) = Multiplicative.ofAdd
      (rho (d.actor s) (d.projection v).toAdd - (d.projection v).toAdd) := by
  let w : Z T a := ⟨s.val*v.val*s.val⁻¹,
    (mem_normalizer_iff.mp (Z_normalized T a s.property) v.val).mp v.property⟩
  have he : seedDisplacement s v = w*v⁻¹ := rfl
  rw [he,map_mul,map_inv,show d.projection w = _ from d.intertwines s v]
  apply Multiplicative.toAdd.injective
  exact (sub_eq_add_neg _ _).symm

include h e in
/-- The literal critical triple lies in the chosen long-root auxiliary modulo
its original residual-fixed kernel. No error term is discarded. -/
theorem critical_triple_le_auxiliary_sup_kernel
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (d : EndpointModel T a) (g : Atlas.G2.Model (ZMod 2))
    (hE : image d (Z T z) = (Atlas.G2.EvenTwoRank.elementary (ZMod 2)).map
      (MulAut.conj g).toMonoidHom)
    (hB : image d (Q T t) ≤ Atlas.G2.unipotent.map (MulAut.conj g).toMonoidHom) :
    ⁅⁅Z T a,Z T z⁆,Q T t⁆ ≤ rootAuxiliary d g ⊔
      d.projection.ker.map (Z T a).subtype := by
  have hz := critical_endpoint_color T a ha _ hc
  let := Z_elementary_of_positive T (geometry h) z hz (by
    rw [(geometry h).distance_constant z hz]; exact (positive_even h e).1)
  let r := MulAut.conj g (Atlas.G2.rootA (1 : ZMod 2))
  have hrE : r ∈ image d (Z T z) := by
    rw [hE]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom
      (Atlas.G2.NaturalOffenders.rootA_mem_elementary 1)
  obtain ⟨s,hs,hsr⟩ := hrE
  rw [commutator_comm]
  apply commutator_le.mpr
  intro b hb x hx
  let b' : stabilizer T a := ⟨b,CriticalCriterion.edge_le_stabilizer T ha hat hb⟩
  let x' : Z T a := ⟨x,critical_image_le_start (geometry h) a z ha hc hx⟩
  have hxfix : (d.projection x').toAdd ∈ fixedSpace rho (image d (Z T z)) := by
    rintro ⟨j,y,hy,rfl⟩
    have hxz := critical_image_le_endpoint (geometry h) a z ha hc hx
    have hcomm : y.val*x = x*y.val :=
      congrArg Subtype.val (mul_comm (⟨y.val,hy⟩ : Z T z) ⟨x,hxz⟩)
    have he : (⟨y.val*x'*y.val⁻¹,
      (mem_normalizer_iff.mp (Z_normalized T a y.property) x'.val).mp x'.property⟩ : Z T a) = x' := by
      apply Subtype.ext
      change y.val*x*y.val⁻¹=x
      rw [hcomm,mul_inv_cancel_right]
    have hh := d.intertwines y x'
    rw [he] at hh
    exact (congrArg Multiplicative.toAdd hh).symm
  obtain ⟨v,hv⟩ := CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour.LongRootModel.natural_displacement
    (image d (Z T z)) (image d (Q T t)) g hE hB (d.actor b')
    (mem_map_of_mem d.actor hb) (d.projection x').toAdd hxfix
  obtain ⟨w,hw⟩ := d.projection_surjective (Multiplicative.ofAdd v)
  have hπ : d.projection (seedDisplacement b' x') = d.projection (seedDisplacement s w) := by
    rw [seedDisplacement_projection,seedDisplacement_projection,hsr,hw]
    exact congrArg Multiplicative.ofAdd hv
  have hA : (seedDisplacement s w).val ∈ rootAuxiliary d g := by
    apply commutator_mem_commutator _ w.property
    exact ⟨s,by change d.actor s ∈ zpowers r; rw [hsr]; exact mem_zpowers r,rfl⟩
  have hK : ((seedDisplacement s w)⁻¹*seedDisplacement b' x').val ∈
      d.projection.ker.map (Z T a).subtype := by
    refine ⟨(seedDisplacement s w)⁻¹*seedDisplacement b' x',?_,rfl⟩
    change d.projection ((seedDisplacement s w)⁻¹*seedDisplacement b' x')=1
    rw [map_mul,map_inv,hπ,inv_mul_cancel]
  have he : ⁅b,x⁆ = (seedDisplacement s w).val *
      ((seedDisplacement s w)⁻¹*seedDisplacement b' x').val := by
    simp only [Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_cancel_left]
    rfl
  rw [he]
  exact mul_mem_sup hA hK

include h e in
/-- Applying the selected auxiliary on the same critical pair makes the
whole critical triple midpoint-fixed modulo the original endpoint kernel.
The residual-fixed error remains explicit for the covering-module step. -/
theorem critical_triple_le_midpoint_fixed_sup_kernel
    (hb : (geometry h).b T = 4)
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t c : Vertex T) (hcColor : color T c = false)
    (hat : Adjacent T a t) (hct : Adjacent T c t)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2)
    (d : EndpointModel T a) :
    ⁅⁅Z T a,Z T z⁆,Q T t⁆ ≤ fixedCore T c ⊔
      d.projection.ker.map (Z T a).subtype := by
  obtain ⟨g,hE,hB,_,hA⟩ := critical_edge_root_auxiliary h e hb a z ha hc t c hcColor
    hat hct hac hcz d
  exact (critical_triple_le_auxiliary_sup_kernel h e a z ha hc t hat d g hE hB).trans
    (sup_le_sup hA le_rfl)

end CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour
