module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SpanFour

/-!
# Endpoint kernel movement with the full central attachment

The natural fixed-hyperplane calculation lifts to the original cover only
modulo its actual central kernel. Thus the edge moves a small actor's fixed
subgroup into the actor commutator joined with the moved central attachment.
This retains the four-coordinate displacement of the order-thirty-two cover;
it is not identified with the complementary critical duad line.

Transport through the original edge embedding gives the same estimate for
full graph seeds and for the reverse critical kernel at its last predecessor.
The moved central attachment has order at most two at every original vertex.
Normal generation also identifies the entire selected-span/forward-kernel
commutator with the forward line, without assuming that the span is nonabelian.

For a small forward slice at distance four, these estimates have an actual
critical-path application: either the desired endpoint commutator lies in the
starting seed, or the endpoint's moved central attachment has order two and
lies in that starting seed. The proof uses the proved disjointness of the
critical line from the starting stabilizer center. The second alternative
remains to be excluded; this is not a proof of the endpoint estimate or of
MS93 (5.12). The nonabelian-span, opposite-core and other-radical-image
obligations also remain with the large-distance assembly owner.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.7)--(5.8) and the endpoint-kernel comparison in (5.12), printed
pp.919--920 and 924--927. Uses the actual replacement, graph, quotient map
and both permitted central covers.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

private theorem cover_moved_preimage (A : Subgroup d.overgroup)
    (v : Additive (replacementMoved d))
    (hv : coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d) v ∈
      subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map s.projection)) :
    (v.toMul : d.overgroup) ∈ ⁅replacementMoved d,A⁆ ⊔ (replacementMoved d ⊓ center d.overgroup) := by
  let := replacementMoved_normal h d
  let π := coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)
  have hm : (NormalElementaryQuotient.commutatorSpace (replacementMoved d) A).map π =
      subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map s.projection) := by
    rw [NormalElementaryQuotient.commutatorSpace_eq (replacementMoved d) s.projection
      s.surjective (s.projection_kernel.trans (moved_centralizer s).symm)]
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
      (coverAction s) (MonoidHom.id S) π (fun g w => (coverMap_equivariant s g w).symm)
      (A.map s.projection) ⊤
    rw [Submodule.map_top,LinearMap.range_eq_top.mpr (coverMap_surjective
      (h := h) (e := e) (hz := hz) (hn := hn) (d := d)),Subgroup.map_id] at hh
    exact hh.symm
  rw [←hm] at hv
  obtain ⟨w,hw,he⟩ := hv
  have hk : v-w ∈ π.ker := by
    rw [LinearMap.mem_ker,map_sub,he,sub_self]
  have hkc : ((v-w).toMul : d.overgroup) ∈ center d.overgroup := by
    have hker : (v-w).toMul ∈ (coverProjection h e hz hn d).ker := hk
    rwa [coverProjection_kernel_center s] at hker
  have hwc : (w.toMul : d.overgroup) ∈ ⁅replacementMoved d,A⁆ := hw
  have hh := (⁅replacementMoved d,A⁆ ⊔ (replacementMoved d ⊓ center d.overgroup)).mul_mem
    (mem_sup_right ⟨(v-w).toMul.property,hkc⟩) (mem_sup_left hwc)
  simpa only [toMul_sub,Subgroup.coe_mul,Subgroup.coe_inv,div_eq_mul_inv,
    inv_mul_cancel_right] using hh

/-- The full cover retains the central attachment in the fixed-edge bound. -/
theorem cover_small_fixed_edge_le_commutator_sup_attachment (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup d.overgroup) (hA : A ≤ d.radical)
    (hne : ¬ A ≤ pCore 2 d.overgroup)
    (hindex : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2) :
    ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),d.radical⁆ ≤
      ⁅replacementMoved d,A⁆ ⊔ (replacementMoved d ⊓ center d.overgroup) := by
  let := replacementMoved_normal h d
  let π := coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)
  have hsmall : fixedCodim (coverAction s) (A.map s.projection) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction s) (naturalRepresentation (Fin 6))
      π (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_equivariant s) (A.map s.projection)).trans hsmall
  have hnA : A.map s.projection ≠ ⊥ := by
    intro he
    exact hne (s.projection_kernel ▸ (map_eq_bot_iff A).mp he)
  have hbound := PointCoreTranspositionFixed.small_image_fixed_displacement_le u
    (A.map s.projection) ((map_mono hA).trans hR) hnA hnat
  apply commutator_le.mpr
  intro v hv r hr
  have hcu : ⁅v,r⁆ ∈ replacementMoved d := (commutator_le_left _ _)
    (commutator_mem_commutator hv.1 hr)
  apply cover_moved_preimage s A (Additive.ofMul ⟨⁅v,r⁆,hcu⟩)
  have hfix : π (Additive.ofMul ⟨v,hv.1⟩) ∈
      fixedSpace (naturalRepresentation (Fin 6)) (A.map s.projection) := by
    have hvf := (NormalElementaryQuotient.mem_fixedSpace_image (replacementMoved d)
      s.projection s.surjective (s.projection_kernel.trans (moved_centralizer s).symm)
      A (Additive.ofMul ⟨v,hv.1⟩)).mpr hv.2
    intro a
    exact (coverMap_equivariant s a _).symm.trans (congrArg π (hvf a))
  have hm : naturalRepresentation (Fin 6) (s.projection r)
      (π (Additive.ofMul ⟨v,hv.1⟩)) - π (Additive.ofMul ⟨v,hv.1⟩) ∈
        subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map s.projection) :=
    hbound (Submodule.subset_span ⟨s.projection r,hR (mem_map_of_mem _ hr),_,hfix,rfl⟩)
  change π (Additive.ofMul ⟨⁅v,r⁆,hcu⟩) ∈ _
  rw [NormalElementaryQuotient.vector_commutator (replacementMoved d) s.projection
    s.surjective (s.projection_kernel.trans (moved_centralizer s).symm) ⟨v,hv.1⟩ r,
    map_sub]
  change π (Additive.ofMul ⟨v,hv.1⟩) -
    π (coverAction s (s.projection r) (Additive.ofMul ⟨v,hv.1⟩)) ∈ _
  rw [coverMap_equivariant s]
  simpa only [neg_sub] using
    (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map s.projection)).neg_mem hm

/-- The fixed-edge bound on the full graph seed, including its actual central attachment. -/
theorem small_edge_fixed_le_commutator_sup_attachment_at (hc : DistanceTwo.CentralLayer d) (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex d.radical} (hcol : color d.radical c = false)
    (hct : Adjacent d.radical c t)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical t)
    (hne : ¬ A ≤ Q d.radical c)
    (hindex : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2) :
    ⁅Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)),Q d.radical t⁆ ≤
      ⁅U d.radical c,A⁆ ⊔ (U d.radical c ⊓
        centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))) := by
  have hcoords : ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧ i.range = stabilizer d.radical c ∧
      d.radical.map i = Q d.radical t ∧ (pCore 2 d.overgroup).map i = Q d.radical c ∧
      (replacementMoved d).map i = U d.radical c := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_,?_⟩
      · have he := stabilizer_act d.radical g (alpha d.radical)
        rw [alpha,act_mVertex,one_mul,stabilizer_m_base] at he
        simpa only [i,MonoidHom.range_comp,Mbar] using he.symm
      · have he := Q_act d.radical g (beta d.radical)
        rw [Q_beta] at he
        simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
      · have he := Q_act d.radical g (alpha d.radical)
        rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      · have he := U_act d.radical g (alpha d.radical)
        rw [hc.U_eq_moved] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · rw [hg.1] at hcol
      cases hcol
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := hcoords
  have hAi : A ≤ i.range := hA.trans (hiR ▸ map_le_range i _)
  have hmA : (A.comap i).map i = A := map_comap_eq_self hAi
  have hAr : A.comap i ≤ d.radical := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmA,hiR]
  have hAn : ¬ A.comap i ≤ pCore 2 d.overgroup := by
    intro hh
    apply hne
    have hm := map_mono (f := i) hh
    rwa [hmA,hiQ] at hm
  have hidx : (centralizer (A.comap i : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hindex
    exact hindex
  have hbound_quotient := map_mono (f := i)
    (cover_small_fixed_edge_le_commutator_sup_attachment s u hR (A.comap i) hAr hAn hidx)
  rw [map_commutator,←map_inf_centralizer_of_injective i hi,hiU,hmA,hiR,
    Subgroup.map_sup,map_commutator,hiU,hmA] at hbound_quotient
  have hatt : (replacementMoved d ⊓ center d.overgroup).map i ≤
      U d.radical c ⊓ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨hiU ▸ mem_map_of_mem i hx.1,?_⟩
    intro y hy
    obtain ⟨m,rfl⟩ := hir ▸ hy
    simpa only [←map_mul] using congrArg i ((mem_center_iff.mp hx.2) m)
  let F := U d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [hcol] at hh
    cases he : color d.radical t <;> simp_all
  have hseed : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hseedA := hseed.trans (centralizer_le hA)
  have hseedN : Z d.radical t ≤ normalizer (U d.radical c : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical hcol hct).trans (Z_le_stabilizer d.radical c)).trans (U_normalized c)
  have heq : Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)) = F ⊔ Z d.radical t := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d hcol hct,
      sup_comm (U d.radical c),inf_centralizer_sup_of_centralizing _ _ _ hseedN hseedA]
    exact sup_comm _ _
  have hbound : ⁅F ⊔ Z d.radical t,Q d.radical t⁆ ≤ ⁅F,Q d.radical t⁆ := by
    apply commutator_le.mpr
    intro x hx r hr
    have hn : Z d.radical t ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
      (le_inf hseedN (hseedA.trans (centralizer (A : Set (FreeAmalgam d.radical))).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
    have hp : x ∈ (F : Set (FreeAmalgam d.radical)) * (Z d.radical t : Set (FreeAmalgam d.radical)) := by
      rw [←coe_mul_of_right_le_normalizer_left F (Z d.radical t) hn]
      exact hx
    obtain ⟨w,hw,z,hz,rfl⟩ := hp
    have hzero : ⁅z,r⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hseed hz r hr).symm
    rw [commutatorElement_mul_left_eq_conj_mul,hzero,mul_one,mul_inv_cancel,one_mul]
    exact commutator_mem_commutator hw hr
  rw [heq]
  exact hbound.trans (hbound_quotient.trans (sup_le_sup_left hatt _))

/-- The last predecessor bounds the full reverse critical kernel, with the central attachment retained. -/
theorem small_critical_kernel_predecessor_le_commutator_sup_attachment
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    ⁅Z d.radical a' ⊓ Q d.radical a,
      Q d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
        ⁅Z d.radical a,Z d.radical a'⁆ ⊔ (U d.radical a' ⊓
          centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical))) := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let t := p.walk.getVert (p.walk.length-1)
  have hat : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.end_color] at hh
    cases he : color d.radical t <;> simp_all
  have hpred : Q d.radical (p.walk.getVert (p.walk.length-2)) ≤ Q d.radical t := by
    apply Q_le_adjacent_h d.radical ht
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hZt : Z d.radical a ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ p.start_color)
    rw [(replacementGeometry h d).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-1 < replacementDistance h d
    omega
  have hfixed : Z d.radical a' ⊓ Q d.radical a =
      Z d.radical a' ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color)))
    · intro x hx
      refine ⟨hx.1,?_⟩
      rw [←C_eq_Q s hc a p.start_color]
      exact ⟨critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
        (by rw [(replacementGeometry h d).distance_constant a p.start_color]
            exact replacementDistance_pos h d) p.critical hx.1,hx.2⟩
  let := finite_Z d.radical a'
  let : Finite (U d.radical a') := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a')) (inclusion_injective _)
  have hindex : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a') ≤ 2 := by
    have hQC : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a') index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc p hsmall).2
  have hbound := small_edge_fixed_le_commutator_sup_attachment_at s hc u hR p.end_color hat
    (Z d.radical a) hZt p.critical.2 hindex
  rw [←hfixed] at hbound
  have hcomm : ⁅U d.radical a',Z d.radical a⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆ := by
    rw [commutator_comm]
    exact commutator_mono le_rfl (DistanceEight.U_le_Z d.radical a')
  exact (commutator_mono le_rfl hpred).trans (hbound.trans (sup_le_sup_right hcomm _))


include s in
/-- The possible moving central attachment has order at most two at every original vertex. -/
theorem moving_central_attachment_card (hc : DistanceTwo.CentralLayer d)
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    Nat.card (U d.radical a ⊓ centralizer
      (stabilizer d.radical a : Set (FreeAmalgam d.radical)) : Subgroup (FreeAmalgam d.radical)) ≤ 2 := by
  obtain ⟨i,hi,hir,_,hiU⟩ := vertex_coordinates (h := h) hc a ha
  have he : (replacementMoved d ⊓ center d.overgroup).map i =
      U d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      refine ⟨hiU ▸ mem_map_of_mem i hx.1,?_⟩
      intro y hy
      obtain ⟨m,rfl⟩ := hir ▸ hy
      simpa only [←map_mul] using congrArg i ((mem_center_iff.mp hx.2) m)
    · rintro x ⟨hx,hxc⟩
      rw [←hiU] at hx
      obtain ⟨v,hv,rfl⟩ := hx
      refine mem_map_of_mem i ⟨hv,mem_center_iff.mpr (fun m => hi ?_)⟩
      simpa only [map_mul] using hxc (i m) (hir ▸ (show i m ∈ i.range from ⟨m,rfl⟩))
  have hk : (coverProjection h e hz hn d).ker.map (replacementMoved d).subtype =
      replacementMoved d ⊓ center d.overgroup := by
    rw [coverProjection_kernel_center s,map_comap_eq,range_subtype,inf_comm]
  rw [←he,card_map_of_injective hi,←hk,card_map_of_injective (replacementMoved d).subtype_injective]
  rcases coverProjection_kernel_card s with hcard | hcard <;> omega



include e hz hn in
/-- The full normal span's forward-kernel commutator is the forward line,
without a nonabelianness assumption on the span. -/
theorem small_selected_span_forward_kernel_commutator_knownSimple
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    ⁅P,T⁆ = ⁅U d.radical (p.walk.getVert 2),T⁆ ∧
      ⁅P,T⁆ ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
      ⁅P,T⁆ ≤ Z d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hlayer := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T⁆
  let P := localZSpan d.radical c (alpha d.radical)
  have hfixed : H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
    small_forward_line_central s hlayer hb p hsmall hslice
  have hHN : stabilizer d.radical (alpha d.radical) ≤ normalizer (H : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp hfixed).trans (Subgroup.centralizer_le_normalizer _)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hTQt : T ≤ Q d.radical t := inf_le_left.trans (Q_le_adjacent_h d.radical ht hat)
  have hseed : Z d.radical t ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
    intro z hz x hx
    rw [Z,if_neg (by simp [ht])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2 x (hTQt hx)
  have hTN : stabilizer d.radical (alpha d.radical) ≤ normalizer (T : Set (FreeAmalgam d.radical)) :=
    selected_forward_kernel_normalized hb rfl hat hct
  have hZcG : Z d.radical c ≤ stabilizer d.radical (alpha d.radical) :=
    ((Z_le_localZSpan d.radical c (alpha d.radical)).trans (localZSpan_le_V d.radical (by
      rw [SimpleGraph.dist_comm,p.dist_start (by omega)]))).trans
      ((replacementGeometry h d).V_local _ rfl hb)
  have hZc : ⁅Z d.radical c,T⁆ ≤ H := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d hcol hct]
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical (alpha d.radical))
      _ _ T _ hHN ((DistanceEight.U_le_Z d.radical c).trans hZcG)
      ((adjacent_Z_le d.radical rfl hat).trans (Z_le_stabilizer d.radical _)) le_rfl
    exact (commutator_eq_bot_iff_le_centralizer.mpr hseed).le.trans bot_le
  have hPT : ⁅P,T⁆ ≤ H := by
    dsimp only [P]
    rw [localZSpan_eq_conjugates]
    apply commutator_iSup_le_of_relative_normal (stabilizer d.radical (alpha d.radical)) T _ _ hHN
    · intro g
      have hgmap : (stabilizer d.radical (alpha d.radical)).map
          (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = stabilizer d.radical (alpha d.radical) :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical (alpha d.radical)).le_normalizer
          ((stabilizer d.radical (alpha d.radical)).inv_mem g.property))
      exact (map_mono hZcG).trans_eq hgmap
    · intro g
      have hm := map_mono (f := (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom) hZc
      have hTm : T.map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = T :=
        mem_normalizer_iff_map_conj_eq.mp (hTN ((stabilizer d.radical (alpha d.radical)).inv_mem g.property))
      have hHm : H.map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = H :=
        mem_normalizer_iff_map_conj_eq.mp (hHN ((stabilizer d.radical (alpha d.radical)).inv_mem g.property))
      rwa [map_commutator,hTm,hHm] at hm
  have he : ⁅P,T⁆ = H := le_antisymm hPT
    (commutator_mono ((DistanceEight.U_le_Z d.radical c).trans (Z_le_localZSpan d.radical _ _)) le_rfl)
  exact ⟨he,he ▸ hfixed,hPT.trans ((selected_forward_kernel_line s hlayer hb p hslice).2.trans
    (adjacent_Z_le d.radical rfl hat))⟩


private theorem central_attachment_forced
    {F : Type*} [Group F] (H D C B : Subgroup F) [Finite C]
    (hHD : H ≤ D ⊔ C) (hHB : H ≤ B) (hDB : D ≤ B)
    (hCN : C ≤ normalizer (D : Set F)) (hcard : Nat.card C ≤ 2)
    (hne : ¬ H ≤ D) : C ≤ B ∧ Nat.card C = 2 := by
  obtain ⟨x,hx,hxD⟩ : ∃ x, x ∈ H ∧ x ∉ D := by
    by_contra hno
    apply hne
    intro x hx
    by_contra hxD
    exact hno ⟨x,hx,hxD⟩
  have hprod : x ∈ (D : Set F) * (C : Set F) := by
    rw [←coe_mul_of_right_le_normalizer_left D C hCN]
    exact hHD hx
  obtain ⟨z,hz,c,hc,hzc⟩ := hprod
  change z*c=x at hzc
  have hcB : c ∈ B := by
    have hh := B.mul_mem (B.inv_mem (hDB hz)) (hHB hx)
    rw [←hzc,inv_mul_cancel_left] at hh
    exact hh
  have hcne : c ≠ 1 := by
    intro he
    rw [he,mul_one] at hzc
    exact hxD (hzc ▸ hz)
  let : Finite (C ⊓ B : Subgroup F) := Finite.of_injective
    (inclusion inf_le_left) (inclusion_injective _)
  have hnon : (C ⊓ B : Subgroup F) ≠ ⊥ := by
    intro he
    exact hcne (mem_bot.mp (he ▸ (show c ∈ C ⊓ B from ⟨hc,hcB⟩)))
  have hlo := (one_lt_card_iff_ne_bot (C ⊓ B : Subgroup F)).mpr hnon
  have hup : Nat.card (C ⊓ B : Subgroup F) ≤ Nat.card C := card_le_of_le inf_le_left
  have he : C ⊓ B = C := eq_of_le_of_card_ge inf_le_left (by omega)
  exact ⟨he ▸ (inf_le_right : C ⊓ B ≤ B),by omega⟩

/-- In the remaining small-slice distance-four branch, failure of the literal
endpoint estimate forces the endpoint's central attachment of order two
inside the starting seed. No central attachment is discarded. -/
theorem full_point_four_endpoint_or_central_attachment_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) ∨
      (U d.radical a' ⊓ centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical)) ≤
        Z d.radical (alpha d.radical) ∧
       Nat.card (U d.radical a' ⊓ centralizer
        (stabilizer d.radical a' : Set (FreeAmalgam d.radical)) : Subgroup (FreeAmalgam d.radical)) = 2) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hi := (full_point_four_critical_indices_two_knownSimple hb u hfull p).1
  have hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by omega
  let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
  let Y := P ⊓ Q d.radical (p.walk.getVert 2)
  let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
  let H := ⁅Y,K⁆
  let D := ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆
  let C := U d.radical a' ⊓ centralizer
    (stabilizer d.radical a' : Set (FreeAmalgam d.radical))
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hYQ : Y ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using (inf_le_right : Y ≤ Q d.radical (p.walk.getVert 2))
  by_cases hzero : H = ⊥
  · exact Or.inl (small_critical_predecessor_commutator s hc hb2 p hsmall Y hYQ
      (commutator_eq_bot_iff_le_centralizer.mp hzero))
  · right
    have hspan := small_selected_span_forward_kernel_commutator_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 p hsmall hslice
    have hKT := le_sup_right.trans (selected_forward_kernel_contains_inner_layers (h := h) hb2 p)
    have hHT := commutator_mono (inf_le_left : Y ≤ P) hKT
    have hHB : H ≤ Z d.radical (alpha d.radical) := hHT.trans hspan.2.2
    have hHC : H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
      hHT.trans hspan.2.1
    have hHDC : H ≤ D ⊔ C := by
      dsimp only [H]
      rw [commutator_comm Y K]
      exact (commutator_mono le_rfl hYQ).trans
        (small_critical_kernel_predecessor_le_commutator_sup_attachment s hc hb2 u hf.le p hsmall)
    have hDB : D ≤ Z d.radical (alpha d.radical) :=
      ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
        (DistanceEight.U_le_Z d.radical _)
    have hDGe : D ≤ stabilizer d.radical a' :=
      (((critical_Z_commutator_le_moving (h := h) p).trans inf_le_right).trans
        (DistanceEight.U_le_Z d.radical _)).trans (Z_le_stabilizer d.radical _)
    have hCN : C ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
      ((inf_le_right : C ≤ centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical))).trans
        (centralizer_le hDGe)).trans (Subgroup.centralizer_le_normalizer _)
    have hnot : ¬ H ≤ D := by
      intro hHD
      apply hzero
      exact le_bot_iff.mp ((le_inf hHD hHC).trans_eq
        (small_critical_commutator_inf_centralizer s hc p hsmall))
    let := finite_Z d.radical a'
    let : Finite C := Finite.of_injective
      (inclusion (inf_le_left.trans (DistanceEight.U_le_Z d.radical a'))) (inclusion_injective _)
    exact central_attachment_forced H D C (Z d.radical (alpha d.radical))
      hHDC hHB hDB hCN (moving_central_attachment_card s hc p.end_color) hnot

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
