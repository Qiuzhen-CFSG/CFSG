module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.EndpointModel.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.Comparison.CriticalImage.Model

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# Reciprocal critical images and the entire endpoint fixed kernel

The two given endpoint actions have equal displacement indices: the natural
quotient cannot increase fixed index, while absence of strict G₂ offenders
gives the reverse bound. Hence the specified endpoint image is an offender,
and its full fixed-space preimage is the actual opposite centralizer.
A single displacement covers the natural fixed three-space. Its pointwise
stabilizer then controls every actor centralizing the critical commutator.
At distance two this puts the entire endpoint kernel in the starting X-layer.

This proves both clauses of `EndpointPlacementInput` from the original small
MS-pair, with no assumption that R is Sylow or that the whole core is elementary.
Source: MS93 (3.2)(vii), (3.3), pp.863–868, and (3.6), pp.870–871.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.Comparison.CriticalImage

open Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open ChapterC BinaryMS.MS93
variable {M : Type*} [Group M] [Finite M] {T : Subgroup M}

def image {z : Vertex T} (d : EndpointModel T z)
    (E : Subgroup (FreeAmalgam T)) : Subgroup (Atlas.G2.Model (ZMod 2)) :=
  (E.subgroupOf (stabilizer T z)).map d.actor

def fixedPreimage {z : Vertex T} (d : EndpointModel T z)
    (E : Subgroup (FreeAmalgam T)) : Subgroup (Z T z) :=
  ((fixedSpace rho (image d E)).toAddSubgroup.toSubgroup).comap d.projection

omit [Finite M] in
private theorem image_card {z : Vertex T} (d : EndpointModel T z)
    (E : Subgroup (FreeAmalgam T)) (hE : E ≤ stabilizer T z) :
    Nat.card (image d E) = (Q T z).relIndex E := by
  have hk : d.actor.ker = (Q T z).subgroupOf (stabilizer T z) := by
    rw [←d.actor_kernel,subgroupOf,Subgroup.comap_map_eq_self_of_injective (stabilizer T z).subtype_injective]
  rw [image,←relIndex_ker,hk,subgroupOf,relIndex_comap,map_subgroupOf_eq_of_le hE]

omit [Finite M] in
private theorem fixedPreimage_index {z : Vertex T} (d : EndpointModel T z)
    (E : Subgroup (FreeAmalgam T)) :
    (fixedPreimage d E).index = 2 ^ fixedCodim rho (image d E) := by
  rw [fixedPreimage,Subgroup.index_comap_of_surjective _ d.projection_surjective]
  let F := (fixedSpace rho (image d E)).toAddSubgroup.toSubgroup
  have hc := F.card_mul_index
  have hf : Nat.card F = 2 ^ Module.finrank (ZMod 2) (fixedSpace rho (image d E)) := by
    exact (Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace rho (image d E))).trans (by rw [Nat.card_zmod])
  have he : Nat.card (Multiplicative NaturalSpace) = 2 ^ Module.finrank (ZMod 2) NaturalSpace := by
    exact (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := NaturalSpace)).trans
      (by rw [Nat.card_zmod])
  rw [hf,he,←fixedCodim_add_finrank rho (image d E),add_comm,pow_add] at hc
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hc

omit [Finite M] in
private theorem centralizer_le_fixedPreimage {z : Vertex T} (d : EndpointModel T z)
    (E : Subgroup (FreeAmalgam T)) :
    (centralizer (E : Set (FreeAmalgam T))).subgroupOf (Z T z) ≤ fixedPreimage d E := by
  intro v hv a
  obtain ⟨x,hx,hxa⟩ := a.property
  change rho a.val (d.projection v).toAdd = (d.projection v).toAdd
  rw [←hxa]
  have hh := d.intertwines x v
  have he : (⟨x.val*v.val*x.val⁻¹,
      (mem_normalizer_iff.mp (Z_normalized T z x.property) v.val).mp v.property⟩ : Z T z) = v := by
    apply Subtype.ext
    change x.val*v.val*x.val⁻¹ = v.val
    have hcomm : x.val*v.val = v.val*x.val := hv x hx
    rw [hcomm,mul_inv_cancel_right]
  rw [he] at hh
  exact (congrArg Multiplicative.toAdd hh).symm

private theorem quotient_index_le {z : Vertex T} (d : EndpointModel T z)
    (E : Subgroup (FreeAmalgam T)) :
    2 ^ fixedCodim rho (image d E) ≤ Offenders.displacement (Z T z) E := by
  let := finite_Z T z
  rw [←fixedPreimage_index d E]
  exact Subgroup.index_antitone (centralizer_le_fixedPreimage d E)

omit [Finite M] in
private theorem image_elementary {z : Vertex T} (d : EndpointModel T z)
    (E : Subgroup (FreeAmalgam T)) (hE : E ≤ stabilizer T z)
    (hne : ¬ E ≤ Q T z) [IsElementaryAbelian 2 E] :
    IsElementaryTwo (image d E) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := IsElementaryAbelian.subgroupOf (p := 2) hE
  refine ⟨?_, IsElementaryAbelian.map d.actor⟩
  intro he
  have hi := image_card d E hE
  rw [he,Subgroup.card_bot] at hi
  exact hne (Subgroup.relIndex_eq_one.mp hi.symm)

private theorem rank_le_fixedCodim (A : Subgroup (Atlas.G2.Model (ZMod 2)))
    (hA : IsElementaryTwo A) : rank A ≤ fixedCodim rho A := by
  by_contra h
  apply Atlas.G2.NaturalOffenders.natural_no_strong (F := ZMod 2)
    (n := 1) (by norm_num) (by decide)
  refine ⟨A,hA,?_⟩
  rw [Atlas.G2.NaturalOffenders.natural_fixedCodim_eq]
  exact Nat.lt_of_not_ge h

omit [Finite M] in
private theorem index_le_natural_index {z : Vertex T} (d : EndpointModel T z)
    (E : Subgroup (FreeAmalgam T)) (hE : E ≤ stabilizer T z)
    (hne : ¬ E ≤ Q T z) [IsElementaryAbelian 2 E] :
    (Q T z).relIndex E ≤ 2 ^ fixedCodim rho (image d E) := by
  have helem := image_elementary d E hE hne
  rw [←image_card d E hE,helem.card_eq_two_pow_rank]
  exact Nat.pow_le_pow_right (by decide) (rank_le_fixedCodim _ helem)

private theorem critical_edge_index (g : Geometry T) (hC : EdgeCentralizerCondition T)
    (a z : Vertex T) (ha : color T a = false)
    (hb : 0 < g.b T) (hc : CriticalPair T a z (g.exists_critical a ha)) :
    Offenders.displacement (Z T a) (Z T z) = (Q T z).relIndex (Z T a) := by
  have hba : 0 < criticalDistance T a (g.exists_critical a ha) := by
    rw [g.distance_constant a ha]; exact hb
  obtain ⟨t,hzt,_,hAt⟩ := critical_predecessor T a ha _ hba hc
  have hz := critical_endpoint_color T a ha _ hc
  have he : Z T a ⊓ centralizer (Z T z : Set (FreeAmalgam T)) = Z T a ⊓ Q T z := by
    rw [←hC z t hz hzt,←inf_assoc,inf_of_le_left hAt]
  unfold Offenders.displacement
  rw [←inf_relIndex_left (Z T a),he,inf_relIndex_left]

/-- The original endpoint indices agree; no new critical pair is selected. -/
theorem critical_displacement_eq (g : Geometry T) (hC : EdgeCentralizerCondition T)
    (a z : Vertex T) (ha : color T a = false)
    (hb : 0 < g.b T) (hc : CriticalPair T a z (g.exists_critical a ha))
    (da : EndpointModel T a) (dz : EndpointModel T z) :
    Offenders.displacement (Z T a) (Z T z) =
      Offenders.displacement (Z T z) (Z T a) := by
  have hz := critical_endpoint_color T a ha _ hc
  have hba : 0 < criticalDistance T a (g.exists_critical a ha) := by
    rw [g.distance_constant a ha]; exact hb
  have hbz : 0 < criticalDistance T z (g.exists_critical z hz) := by
    rw [g.distance_constant z hz]; exact hb
  have hrev := critical_reverse T g hC a ha hba z hz hc
  let := Z_elementary_of_positive T g a ha hba
  let := Z_elementary_of_positive T g z hz hbz
  have haz := Z_le_stabilizer_of_dist_le a (g.exists_critical a ha) hc.1.le
  have hza := Z_le_stabilizer_of_dist_le z (g.exists_critical z hz) hrev.1.le
  apply le_antisymm
  · rw [critical_edge_index g hC a z ha hb hc]
    exact (index_le_natural_index dz _ haz hc.2).trans (quotient_index_le dz _)
  · rw [critical_edge_index g hC z a hz hb hrev]
    exact (index_le_natural_index da _ hza hrev.2).trans (quotient_index_le da _)

/-- The literal image of the given opposite endpoint is an offender. -/
theorem critical_image_offender (g : Geometry T) (hC : EdgeCentralizerCondition T)
    (a z : Vertex T) (ha : color T a = false)
    (hb : 0 < g.b T) (hc : CriticalPair T a z (g.exists_critical a ha))
    (da : EndpointModel T a) (dz : EndpointModel T z) :
    IsOffender rho (image dz (Z T a)) := by
  have hba : 0 < criticalDistance T a (g.exists_critical a ha) := by
    rw [g.distance_constant a ha]; exact hb
  let := Z_elementary_of_positive T g a ha hba
  have haz := Z_le_stabilizer_of_dist_le a (g.exists_critical a ha) hc.1.le
  have helem := image_elementary dz (Z T a) haz hc.2
  refine ⟨helem,?_⟩
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [←helem.card_eq_two_pow_rank,image_card dz _ haz,
    ←critical_edge_index g hC a z ha hb hc,critical_displacement_eq g hC a z ha hb hc da dz]
  exact quotient_index_le dz _

/-- There is no extra fixed-vector preimage beyond the actual centralizer. -/
theorem critical_fixed_preimage (g : Geometry T) (hC : EdgeCentralizerCondition T)
    (a z : Vertex T) (ha : color T a = false)
    (hb : 0 < g.b T) (hc : CriticalPair T a z (g.exists_critical a ha))
    (da : EndpointModel T a) (dz : EndpointModel T z) :
    fixedPreimage dz (Z T a) =
      (centralizer (Z T a : Set (FreeAmalgam T))).subgroupOf (Z T z) := by
  let := finite_Z T z
  have hba : 0 < criticalDistance T a (g.exists_critical a ha) := by
    rw [g.distance_constant a ha]; exact hb
  let := Z_elementary_of_positive T g a ha hba
  have haz := Z_le_stabilizer_of_dist_le a (g.exists_critical a ha) hc.1.le
  have hle := centralizer_le_fixedPreimage dz (Z T a)
  by_contra hne
  have hlt := Subgroup.index_strictAnti (lt_of_le_of_ne hle (Ne.symm hne))
  have hlow := index_le_natural_index dz (Z T a) haz hc.2
  rw [←critical_edge_index g hC a z ha hb hc,
    critical_displacement_eq g hC a z ha hb hc da dz,
    ←fixedPreimage_index dz (Z T a)] at hlow
  exact (not_lt_of_ge hlow) hlt

/-- In particular the entire endpoint projection kernel centralizes the
original opposite seed. -/
theorem critical_kernel_centralizes (g : Geometry T) (hC : EdgeCentralizerCondition T)
    (a z : Vertex T) (ha : color T a = false)
    (hb : 0 < g.b T) (hc : CriticalPair T a z (g.exists_critical a ha))
    (da : EndpointModel T a) (dz : EndpointModel T z) :
    dz.projection.ker.map (Z T z).subtype ≤
      centralizer (Z T a : Set (FreeAmalgam T)) := by
  rintro x ⟨v,hv,rfl⟩
  have hf : v ∈ fixedPreimage dz (Z T a) := by
    change (dz.projection v).toAdd ∈ fixedSpace rho (image dz (Z T a))
    change dz.projection v = 1 at hv
    rw [hv]
    exact Submodule.zero_mem _
  rw [critical_fixed_preimage g hC a z ha hb hc da dz] at hf
  exact hf

-- Appended to the checked model and reciprocal calculations.
open scoped commutatorElement

/-- Every vector in the offender fixed three-space lifts to an actual critical
commutator, with the specified endpoint projection. -/
theorem critical_fixed_covered (g : Geometry T) (hC : EdgeCentralizerCondition T)
    (a z : Vertex T) (ha : color T a = false)
    (hb : 0 < g.b T) (hc : CriticalPair T a z (g.exists_critical a ha))
    (da : EndpointModel T a) (dz : EndpointModel T z) :
    ∀ w ∈ fixedSpace rho (image dz (Z T a)), Multiplicative.ofAdd w ∈
      ((⁅Z T a,Z T z⁆).subgroupOf (Z T z)).map dz.projection := by
  have hoff := critical_image_offender g hC a z ha hb hc da dz
  obtain ⟨t,ht,he⟩ := Atlas.G2.Natural.BinaryIsotropicThree.offender_fixed_is_single_displacement
    (image dz (Z T a)) hoff
  obtain ⟨x,hx,rfl⟩ := ht
  intro w hw
  rw [he] at hw
  obtain ⟨v,hv⟩ := hw
  obtain ⟨u,hu⟩ := dz.projection_surjective (Multiplicative.ofAdd v)
  have hD : ⁅x.val,u.val⁆ ∈ ⁅Z T a,Z T z⁆ := commutator_mem_commutator hx u.property
  have hZ := critical_image_le_endpoint g a z ha hc hD
  refine ⟨⟨⁅x.val,u.val⁆,hZ⟩,hD,?_⟩
  have hcπ : dz.projection ⟨⁅x.val,u.val⁆,hZ⟩ =
      dz.projection ⟨x.val*u.val*x.val⁻¹,
        (mem_normalizer_iff.mp (Z_normalized T z x.property) u.val).mp u.property⟩ *
      (dz.projection u)⁻¹ := by
    rw [←map_inv,←map_mul]
    rfl
  rw [hcπ,dz.intertwines,hu]
  apply Multiplicative.toAdd.injective
  change rho (dz.actor x) v - v = w at hv
  simpa only [toAdd_mul,toAdd_ofAdd,toAdd_inv,sub_eq_add_neg] using hv

/-- Pointwise fixing the critical image forces the full actor into the
opposite seed modulo the exact two-core, so its entire commutator lies in D. -/
theorem critical_commutator_le (g : Geometry T) (hC : EdgeCentralizerCondition T)
    (a z : Vertex T) (ha : color T a = false)
    (hb : 0 < g.b T) (hc : CriticalPair T a z (g.exists_critical a ha))
    (da : EndpointModel T a) (dz : EndpointModel T z)
    (Y : Subgroup (FreeAmalgam T)) (hY : Y ≤ stabilizer T z)
    (hYD : Y ≤ centralizer ((⁅Z T a,Z T z⁆ : Subgroup (FreeAmalgam T)) : Set (FreeAmalgam T))) :
    ⁅Y,Z T z⁆ ≤ ⁅Z T a,Z T z⁆ := by
  have hoff := critical_image_offender g hC a z ha hb hc da dz
  have hcover := critical_fixed_covered g hC a z ha hb hc da dz
  have hz := critical_endpoint_color T a ha _ hc
  have hbz : 0 < criticalDistance T z (g.exists_critical z hz) := by
    rw [g.distance_constant z hz]; exact hb
  have hpoint : ∀ y ∈ Y, ∃ x ∈ Z T a, x⁻¹*y ∈ Q T z := by
    intro y hy
    let y' : stabilizer T z := ⟨y,hY hy⟩
    have hfix : ∀ w ∈ fixedSpace rho (image dz (Z T a)), rho (dz.actor y') w = w := by
      intro w hw
      obtain ⟨c,hcD,hcπ⟩ := hcover w hw
      have he : (⟨y*c.val*y⁻¹,
        (mem_normalizer_iff.mp (Z_normalized T z y'.property) c.val).mp c.property⟩ : Z T z) = c := by
        apply Subtype.ext
        change y*c.val*y⁻¹ = c.val
        rw [←hYD hy c.val hcD,mul_inv_cancel_right]
      have hi := dz.intertwines y' c
      rw [he] at hi
      change dz.projection c = Multiplicative.ofAdd w at hcπ
      simpa only [hcπ,toAdd_ofAdd] using (congrArg Multiplicative.toAdd hi).symm
    obtain ⟨x,hx,hxe⟩ := offender_pointwise_fixed _ hoff (dz.actor y') hfix
    have hker : x⁻¹*y' ∈ dz.actor.ker := by
      change dz.actor (x⁻¹*y') = 1
      rw [map_mul,map_inv,hxe,inv_mul_cancel]
    have hQ : x.val⁻¹*y ∈ Q T z := by
      rw [←dz.actor_kernel]
      exact ⟨x⁻¹*y',hker,rfl⟩
    exact ⟨x.val,hx,hQ⟩
  apply commutator_le.mpr
  intro y hy v hv
  obtain ⟨x,hx,hq⟩ := hpoint y hy
  have hvq := Q_le_centralizer_X T z hq v (g.omega_bound z hz hbz hv)
  have he : y*v*y⁻¹ = x*v*x⁻¹ := by
    have hh := congrArg (fun k => x*k*y⁻¹) hvq.symm
    simpa [mul_assoc] using hh
  change y*v*y⁻¹*v⁻¹ ∈ ⁅Z T a,Z T z⁆
  rw [he]
  exact commutator_mem_commutator hx hv

/-- The full endpoint projection kernel lies in the starting omega-center.
Reciprocity first makes it centralize the starting seed. The pointwise fixer
of the critical three-space then lifts this to the entire starting kernel. -/
theorem critical_kernel_le_X (g : Geometry T) (hC : EdgeCentralizerCondition T)
    (a z : Vertex T) (ha : color T a = false)
    (hb : g.b T = 2) (hc : CriticalPair T a z (g.exists_critical a ha))
    (da : EndpointModel T a) (dz : EndpointModel T z) :
    dz.projection.ker.map (Z T z).subtype ≤ X T a := by
  have hpos : 0 < g.b T := by omega
  have hz := critical_endpoint_color T a ha _ hc
  have hbz : 0 < criticalDistance T z (g.exists_critical z hz) := by
    rw [g.distance_constant z hz]; exact hpos
  have hd : (cosetGraph T).dist a z = 2 :=
    hc.1.trans ((g.distance_constant a ha).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two T a z hd
  have ht : color T t = true := by
    have hn := adjacent_color_ne T hzt
    cases he : color T t <;> simp_all
  have hZt : Z T z ≤ Q T t := (g.omega_bound z hz hbz).trans
    ((omegaCenter_le _).trans (Q_le_adjacent_h T ht hzt))
  have hcentral := critical_kernel_centralizes g hC a z ha hpos hc da dz
  have hoff := critical_image_offender g hC a z ha hpos hc da dz
  have hcover := critical_fixed_covered g hC a z ha hpos hc da dz
  have hQz := Q_le_stabilizer_of_dist_two T a z ha hd
  obtain ⟨_,_,_,hactor⟩ := distance_two_source_actor g a z ha hb hc
  rintro k ⟨v,hv,rfl⟩
  have hkc : v.val ∈ centralizer (Z T a : Set (FreeAmalgam T)) :=
    hcentral ⟨v,hv,rfl⟩
  have hkQ : v.val ∈ Q T a := by
    rw [←hC a t ha hat]
    exact ⟨hZt v.property,hkc⟩
  apply mem_omegaCenter_iff.mpr
  refine ⟨hkQ,(mem_omegaCenter_iff.mp (g.omega_bound z hz hbz v.property)).2.1,?_⟩
  intro q hq
  let q' : stabilizer T z := ⟨q,hQz hq⟩
  have hfix : ∀ w ∈ fixedSpace rho (image dz (Z T a)), rho (dz.actor q') w = w := by
    intro w hw
    obtain ⟨c,hcD,hcπ⟩ := hcover w hw
    have he : q*c.val*q⁻¹ = c.val := by
      rw [←(hactor hq).2 c.val hcD,mul_inv_cancel_right]
    have hi := dz.intertwines q' c
    have he' : (⟨q*c.val*q⁻¹,
      (mem_normalizer_iff.mp (Z_normalized T z q'.property) c.val).mp c.property⟩ : Z T z) = c :=
      Subtype.ext he
    rw [he'] at hi
    change dz.projection c = Multiplicative.ofAdd w at hcπ
    simpa only [hcπ,toAdd_ofAdd] using (congrArg Multiplicative.toAdd hi).symm
  have hmem := offender_pointwise_fixed _ hoff (dz.actor q') hfix
  obtain ⟨x,hx,hxe⟩ := hmem
  have hker : q'*x⁻¹ ∈ dz.actor.ker := by
    change dz.actor (q'*x⁻¹) = 1
    rw [map_mul,map_inv,hxe,mul_inv_cancel]
  have hQ : q*x.val⁻¹ ∈ Q T z := by
    rw [←dz.actor_kernel]
    exact ⟨q'*x⁻¹,hker,rfl⟩
  have hcv := Q_le_centralizer_X T z hQ v.val (g.omega_bound z hz hbz v.property)
  have hcx := hkc x.val hx
  have hcq : q ∈ centralizer ({v.val} : Set (FreeAmalgam T)) := by
    have hc1 : q*x.val⁻¹ ∈ centralizer ({v.val} : Set (FreeAmalgam T)) := by
      intro y hy
      have hy' : y = v.val := Set.mem_singleton_iff.mp hy
      subst y
      exact hcv
    have hc2 : x.val ∈ centralizer ({v.val} : Set (FreeAmalgam T)) := by
      intro y hy
      have hy' : y = v.val := Set.mem_singleton_iff.mp hy
      subst y
      exact hcx.symm
    have hh := (centralizer ({v.val} : Set (FreeAmalgam T))).mul_mem hc1 hc2
    simpa only [inv_mul_cancel_right] using hh
  exact (hcq v.val (Set.mem_singleton _)).symm

/-- The entire critical-image and fixed-kernel placements for the literal
endpoint marking, at critical distance two. -/
theorem endpointPlacement_of_models (g : Geometry T) (hC : EdgeCentralizerCondition T)
    (a z : Vertex T) (ha : color T a = false)
    (hb : g.b T = 2) (hc : CriticalPair T a z (g.exists_critical a ha))
    (da : EndpointModel T a) (dz : EndpointModel T z) : EndpointPlacement T a z dz := by
  have hpos : 0 < g.b T := by omega
  refine ⟨critical_kernel_le_X g hC a z ha hb hc da dz,
    fixedSpace rho (image dz (Z T a)),?_,critical_fixed_covered g hC a z ha hpos hc da dz⟩
  exact offender_fixed_orthogonal _ (critical_image_offender g hC a z ha hpos hc da dz)

universe u
/-- The actual Pair supplies both endpoint markings and edge centralizers. -/
theorem endpointPlacement_knownSimple : EndpointPlacementInput.{u} := by
  intro J _ _ L R h e hb z hc dz
  obtain ⟨da⟩ := endpointModel_knownSimple h e (z := alpha _) rfl
  exact endpointPlacement_of_models (geometry h) (edgeCentralizer h e)
    (alpha _) z rfl hb hc da dz

end CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.Comparison.CriticalImage
