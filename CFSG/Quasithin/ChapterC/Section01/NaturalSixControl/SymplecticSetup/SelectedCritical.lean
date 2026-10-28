module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.LargeDistance
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.RadiusComplete
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardKernel
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.NoncentralSeedChoice
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.OddCriticalActor

/-!
# Centrality and small images on selected native critical paths

The first edge kernel normalizes a critical commutator: its image is abelian,
so its conjugation changes the opposite layer only by elements centralizing
the starting layer. For two consecutive selected paths, the recorded edge
kernel and the next endpoint generate the midpoint stabilizer. The latter
endpoint centralizes the first commutator, hence that commutator is normal at
the midpoint. Radius centrality makes the midpoint two-core centralize it.

Every native critical image contains an odd permutation. The centralizer of
the normal commutator therefore maps onto all of S6 and is the whole midpoint
stabilizer. The commutator lies in the moving fixed line of its first edge,
so it has order at most two. The natural fixed-index bound forces both actual
critical images to have order two. All statements retain the same selected
paths and their literal generating edge; arbitrary-path smallness is not used.

The SourceData application retains the characteristic replacement and its
separate alternating-block alternative. This contracts the large-image branch
of MS93 (5.12)(2), printed pp.925--926, in the full native point-core case.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)
private theorem fixed_mod_central_normalizes {G : Type*} [Group G]
    (A Q D : Subgroup G) (hAQ : A ≤ normalizer (Q : Set G))
    (hDQ : D ≤ normalizer (Q : Set G))
    (hDA : ⁅D,A⁆ ≤ centralizer (Q : Set G)) :
    D ≤ normalizer ((⁅A,Q⁆ : Subgroup G) : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro d hd _ ⟨a,ha,q,hq,rfl⟩
  have hq' : d*q*d⁻¹ ∈ Q := (mem_normalizer_iff.mp (hDQ hd) q).mp hq
  have hk : ⁅d,a⁆ ∈ centralizer (Q : Set G) := hDA (commutator_mem_commutator hd ha)
  have hcomm : ⁅a,d*q*d⁻¹⁆ ∈ Q :=
    le_normalizer_iff_commutator_le_right.mp hAQ (commutator_mem_commutator ha hq')
  have hzero : ⁅⁅d,a⁆,d*q*d⁻¹⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hk _ hq').symm
  rw [conjugate_commutatorElement,show d*a*d⁻¹ = ⁅d,a⁆*a by
    simp [commutatorElement_def,mul_assoc],commutatorElement_mul_left_eq_conj_mul,
    hzero,mul_one,←hk _ hcomm,mul_inv_cancel_right]
  exact commutator_mem_commutator ha hq'


theorem critical_commutator_normalized_first
    (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    {a e : Vertex R} (p : CriticalPath R s.geometry a e) :
    Q R (p.walk.getVert 1) ≤ normalizer ((⁅Z R a,Z R e⁆:Subgroup (FreeAmalgam R)):Set (FreeAmalgam R)) := by
  let D := ⁅Z R a,Z R e⁆
  let t := p.walk.getVert 1
  have hpos : 0<p.walk.length := p.length_eq_b ▸ s.criticalDistance_pos
  have hat : Adjacent R a t := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero,Nat.zero_add] using
      p.walk.adj_getVert_succ (i:=0) hpos
  have ht : color R t=true := by
    have hn := adjacent_color_ne R hat
    rw [p.start_color] at hn
    cases hc : color R t <;> simp_all
  have hZe : Z R e≤Q R t := by
    apply Z_le_Q_of_dist_lt R e (s.geometry.exists_critical e p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,s.geometry.distance_constant e p.end_color]
    change p.walk.length-1<s.geometry.b R
    rw [←p.length_eq_b]
    omega
  have hQtG : Q R t≤stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hQtZ := hQtG.trans (Z_normalized R a)
  have hder : ⁅Q R t,Z R e⁆≤centralizer (Z R a:Set (FreeAmalgam R)) :=
    ((commutator_mono le_rfl hZe).trans (s.edge_derived_le_kernel u hfull p.start_color hat)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R a p.start_color)))
  exact (show Q R t≤normalizer (D:Set (FreeAmalgam R)) from by
    dsimp only [D]
    rw [commutator_comm (Z R a)]
    exact fixed_mod_central_normalizes (Z R e) (Z R a) (Q R t)
      (hZe.trans hQtZ) hQtZ hder)

omit [Finite M] in
private theorem normal_eq_top_of_odd_image
    (hq : Function.Surjective s.projection)
    (N : Subgroup M) [N.Normal] (hk : pCore 2 M≤N)
    (hodd : ¬ N.map s.projection≤alternatingGroup (Fin 6)) : N=⊤ := by
  have hne : ¬ N≤pCore 2 M := by
    intro hh
    apply hodd
    rw [show N.map s.projection=⊥ from
      (map_eq_bot_iff N).mpr (hh.trans_eq s.projection_kernel.symm)]
    exact bot_le
  have hL := s.component_le_normal_of_not_le_core hq N hne
  have hAlt : alternatingGroup (Fin 6)≤N.map s.projection := by
    rw [←s.component_image]
    exact map_mono hL
  obtain ⟨a,ha,hodd⟩ := SetLike.not_le_iff_exists.mp hodd
  have hsign : Equiv.Perm.sign a = -1 :=
    (Int.units_eq_one_or _).resolve_left (fun h => hodd (Equiv.Perm.mem_alternatingGroup.mpr h))
  have htop : N.map s.projection=⊤ := by
    apply top_unique
    intro x _
    by_cases hx : x∈alternatingGroup (Fin 6)
    · exact hAlt hx
    · have hxsign : Equiv.Perm.sign x = -1 :=
        (Int.units_eq_one_or _).resolve_left (fun h => hx (Equiv.Perm.mem_alternatingGroup.mpr h))
      have hmem : x*a⁻¹∈alternatingGroup (Fin 6) := by
        rw [Equiv.Perm.mem_alternatingGroup,map_mul,map_inv,hxsign,hsign]
        decide
      have hh := (N.map s.projection).mul_mem (hAlt hmem) ha
      simpa only [inv_mul_cancel_right] using hh
  have he := comap_map_eq_self (f:=s.projection) (H:=N) (s.projection_kernel ▸ hk)
  rw [htop,comap_top] at he
  exact he.symm

private theorem normalized_subgroup_central_of_critical_odd
    (hq : Function.Surjective s.projection)
    (D A : Subgroup (FreeAmalgam R))
    (hD : D≤stabilizer R (alpha R))
    (hn : stabilizer R (alpha R)≤normalizer (D:Set (FreeAmalgam R)))
    (hQ : Q R (alpha R)≤centralizer (D:Set (FreeAmalgam R)))
    (hAC : A≤centralizer (D:Set (FreeAmalgam R)))
    (hodd : ¬ (A.comap (embedM R)).map s.projection≤alternatingGroup (Fin 6)) :
    D≤centralizer (stabilizer R (alpha R):Set (FreeAmalgam R)) := by
  let D₀ := D.comap (embedM R)
  let N := centralizer (D₀:Set M)
  have hDm : D₀.map (embedM R)=D := map_comap_eq_self (hD.trans_eq (stabilizer_m_base R))
  have hg (m:M) : embedM R m∈stabilizer R (alpha R) := by
    change embedM R m∈stabilizer R (mVertex R 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  let : D₀.Normal := ⟨by
    intro d hd m
    change embedM R (m*d*m⁻¹)∈D
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hn (hg m)) _).mp hd⟩
  let : N.Normal := inferInstance
  have hk : pCore 2 M≤N := by
    intro m hm d hd
    apply embedM_injective R
    simp only [map_mul]
    exact hQ (by rw [Q_alpha R s.two_group s.core_le]; exact mem_map_of_mem _ hm) _ hd
  have hAN : A.comap (embedM R)≤N := by
    intro a ha d hd
    apply embedM_injective R
    simp only [map_mul]
    exact hAC ha _ hd
  have htop : N=⊤ := s.normal_eq_top_of_odd_image hq N hk
    (fun hh => hodd ((map_mono hAN).trans hh))
  rintro d hd g hg'
  obtain ⟨m,rfl⟩ := (show stabilizer R (alpha R)≤(embedM R).range from
    (stabilizer_m_base R).le) hg'
  obtain ⟨x,hx,rfl⟩ := hDm.symm ▸ hd
  have hc : m∈N := htop ▸ mem_top m
  simpa only [map_mul] using (congrArg (embedM R) (hc x hx)).symm


theorem selected_critical_commutator_central
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2<s.geometry.b R) {m c e : Vertex R}
    (p : CriticalPath R s.geometry m c) (q : CriticalPath R s.geometry (alpha R) e)
    (hm : (cosetGraph R).dist m (alpha R)≤2)
    (hc : (cosetGraph R).dist c (alpha R)≤2)
    (hce : (cosetGraph R).dist c e<s.geometry.b R)
    (hgen : Q R (p.walk.getVert 1)⊔Z R e=stabilizer R (alpha R)) :
    ⁅Z R m,Z R c⁆≤centralizer (stabilizer R (alpha R):Set (FreeAmalgam R)) := by
  let D := ⁅Z R m,Z R c⁆
  have hVm : Z R m≤V R (alpha R) :=
    le_iSup_of_le m (le_iSup_of_le hm le_rfl)
  have hVc : Z R c≤V R (alpha R) :=
    le_iSup_of_le c (le_iSup_of_le hc le_rfl)
  have hpoint : R.map s.projection≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull.le
  have hDX : D≤X R (alpha R) :=
    (commutator_mono hVm hVc).trans
      ((s.radius_bounds_of_two_lt h u hpoint hb rfl m c).2.1)
  have hDQ : D≤Q R (alpha R) := hDX.trans (omegaCenter_le _)
  have hQC : Q R (alpha R)≤centralizer (D:Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mp
    exact hDX.trans (fun _ hx => (mem_omegaCenter_iff.mp hx).2.2)
  have hDc : D≤Z R c := (s.critical_Z_commutator_le_moving p).trans inf_le_right |>.trans
    (DistanceEight.U_le_Z R c)
  have hC : Z R e≤centralizer (D:Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mp
    apply (hDc.trans (Z_le_Q_of_dist_lt R c (s.geometry.exists_critical c p.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R e q.end_color)))
    rw [s.geometry.distance_constant c p.end_color]
    exact hce
  have hN : stabilizer R (alpha R)≤normalizer (D:Set (FreeAmalgam R)) := by
    rw [←hgen]
    exact sup_le (s.critical_commutator_normalized_first u hfull p)
      (hC.trans (Subgroup.centralizer_le_normalizer _))
  exact s.normalized_subgroup_central_of_critical_odd
    (s.projection_surjective_of_radical_image_le_conjugate u hfull.le)
    D (Z R e) (hDQ.trans (fun _ hx => hx.1)) hN hQC hC
    (s.critical_opposite_image_not_le_alternating h u hpoint q)


theorem critical_image_lt_four_of_commutator_card_le_two
    (h : NativeCentralLayer s) (hq : Function.Surjective s.projection)
    {a e : Vertex R} (p : CriticalPath R s.geometry a e)
    (hcard : Nat.card (⁅Z R a,Z R e⁆:Subgroup (FreeAmalgam R))≤2) :
    (Q R e).relIndex (Z R a)<4 := by
  by_contra hn
  have hforward : 4≤(Q R e).relIndex (Z R a) := by omega
  obtain ⟨g,hg⟩ := exists_mVertex_of_color R p.end_color
  let j := (MulAut.conj g⁻¹).toMonoidHom
  let i := j.comp (embedM R)
  have hi : Function.Injective i := (MulAut.conj g⁻¹).injective.comp (embedM_injective R)
  have hact : act R g (alpha R)=e := by rw [hg]; simp only [alpha,act_mVertex,one_mul]
  have hQ : (pCore 2 M).map i=Q R e := by
    rw [←hact,Q_act,Q_alpha R s.two_group s.core_le,map_map]
  have hU : W.map i=U R e := by rw [←hact,U_act,h.U_eq_module,map_map]
  have hG : i.range=stabilizer R e := by
    rw [←hact,stabilizer_act]
    change (j.comp (embedM R)).range=(stabilizer R (mVertex R 1)).map j
    rw [stabilizer_m_base,MonoidHom.range_comp]
    rfl
  have hA : Z R a ≤ i.range := by
    rw [hG]
    exact Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  let := s.geometry.Z_elementary s.criticalDistance_pos a p.start_color
  have hidx : 4≤(centralizer (Z R a:Set (FreeAmalgam R))).relIndex (U R e) := by
    rw [←hU]
    apply s.embedded_centralizing_index_four_le i hi (Z R a) _ hA le_rfl
    rwa [hQ]
  rw [s.moving_fixedIndex_eq_commutator_card h hq e p.end_color (Z R a)
    (hA.trans_eq hG)] at hidx
  let := finite_Z R a
  let : Finite (⁅Z R a,Z R e⁆:Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion ((s.critical_Z_commutator_le_moving p).trans inf_le_left |>.trans
      (DistanceEight.U_le_Z R a))) (inclusion_injective _)
  have hle : ⁅U R e,Z R a⁆≤⁅Z R a,Z R e⁆ := by
    rw [commutator_comm (Z R a)]
    exact commutator_mono (DistanceEight.U_le_Z R e) le_rfl
  have hc := (card_le_of_le hle).trans hcard
  omega

theorem selected_critical_commutator_card_le_two
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2<s.geometry.b R) {m c e : Vertex R}
    (p : CriticalPath R s.geometry m c) (q : CriticalPath R s.geometry (alpha R) e)
    (hm : (cosetGraph R).dist m (alpha R)≤2)
    (hc : (cosetGraph R).dist c (alpha R)≤2)
    (hce : (cosetGraph R).dist c e<s.geometry.b R)
    (hgen : Q R (p.walk.getVert 1)⊔Z R e=stabilizer R (alpha R)) :
    Nat.card (⁅Z R m,Z R c⁆:Subgroup (FreeAmalgam R))≤2 := by
  let D := ⁅Z R m,Z R c⁆
  let t := p.walk.getVert 1
  have hpos : 0<p.walk.length := p.length_eq_b ▸ s.criticalDistance_pos
  have hmt : Adjacent R m t := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero,Nat.zero_add] using
      p.walk.adj_getVert_succ (i:=0) hpos
  have ht : color R t≠false := by
    exact (adjacent_color_ne R hmt) ∘ (fun he => p.start_color.trans he.symm)
  have hD : D≤U R m := (s.critical_Z_commutator_le_moving p).trans inf_le_left
  have hC := s.selected_critical_commutator_central h u hfull hb p q hm hc hce hgen
  have hQt : Q R t≤stabilizer R (alpha R) := hgen ▸ le_sup_left
  have hZQ : Z R m≤Q R m := by
    apply Z_le_Q_of_dist_lt R m (s.geometry.exists_critical m p.start_color)
    rw [SimpleGraph.dist_self,s.geometry.distance_constant m p.start_color]
    exact s.criticalDistance_pos
  let := s.geometry.Z_elementary s.criticalDistance_pos m p.start_color
  have hDt : D≤Z R t := by
    intro z hz
    have hzZ := (hD.trans (DistanceEight.U_le_Z R m)) hz
    rw [Z,if_neg ht,edgeOmega]
    apply mem_omegaCenter_iff.mpr
    refine ⟨(hZQ.trans (Q_le_adjacent_h R (Bool.eq_true_of_not_eq_false ht) hmt)) hzZ,
      elemPow_eq_one_of_isElementaryAbelian z hzZ,?_⟩
    intro q hq
    exact hC hz q (hQt hq)
  let := finite_Z R t
  let : Finite (U R m⊓Z R t:Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion inf_le_right) (inclusion_injective _)
  exact (card_le_of_le (le_inf hD hDt)).trans_eq (s.moving_inf_edge_card h u hfull p.start_color hmt)


/-- Both images of the same selected critical pair have order two. -/
theorem selected_critical_indices_eq_two
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2<s.geometry.b R) {m c e : Vertex R}
    (p : CriticalPath R s.geometry m c) (q : CriticalPath R s.geometry (alpha R) e)
    (hm : (cosetGraph R).dist m (alpha R)≤2)
    (hc : (cosetGraph R).dist c (alpha R)≤2)
    (hce : (cosetGraph R).dist c e<s.geometry.b R)
    (hgen : Q R (p.walk.getVert 1)⊔Z R e=stabilizer R (alpha R)) :
    (Q R c).relIndex (Z R m)=2 ∧ (Q R m).relIndex (Z R c)=2 := by
  apply s.small_critical_indices h p
  exact s.critical_image_lt_four_of_commutator_card_le_two h
    (s.projection_surjective_of_radical_image_le_conjugate u hfull.le) p
    (s.selected_critical_commutator_card_le_two h u hfull hb p q hm hc hce hgen)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B:Subgroup K)

/-- The same selected paths in the literal characteristic replacement supply
centrality and both order-two critical images. -/
theorem reducedSource_block_or_selected_critical
    (r : CharacteristicReduction (L.subgroupOf J) (d.B.subgroupOf J))
    (hb : 2<((originalSource d hm).reduce r).geometry.b r.radical)
    {m c e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry m c)
    (q : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hmiddle : (cosetGraph r.radical).dist m (alpha r.radical)≤2)
    (hc : (cosetGraph r.radical).dist c (alpha r.radical)≤2)
    (hce : (cosetGraph r.radical).dist c e<((originalSource d hm).reduce r).geometry.b r.radical)
    (hgen : Q r.radical (p.walk.getVert 1)⊔Z r.radical e=stabilizer r.radical (alpha r.radical)) :
    IsAlternatingBlock L 6 ∨
      (⁅Z r.radical m,Z r.radical c⁆≤centralizer
        (stabilizer r.radical (alpha r.radical):Set (FreeAmalgam r.radical)) ∧
        (Q r.radical c).relIndex (Z r.radical m)=2 ∧
        (Q r.radical m).relIndex (Z r.radical c)=2) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock | hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    have h := reduced_nativeCentralLayer d hm r
    exact ⟨s.selected_critical_commutator_central h _ hf hb p q hmiddle hc hce hgen,
      s.selected_critical_indices_eq_two h _ hf hb p q hmiddle hc hce hgen⟩
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
