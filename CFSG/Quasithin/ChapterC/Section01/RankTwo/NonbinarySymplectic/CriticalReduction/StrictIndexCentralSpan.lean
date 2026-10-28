module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexCentral
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.StrictIndex.Span
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.StrictIndex.Seed

/-!
# The full central orbit in the strict-index countercase

After the noncentral branch is excluded, H centralizes the starting vertex.
Consequently every conjugate seed has the same complete T₀-displacement H,
and the full vertex orbit has precisely that displacement. If H escapes
both terminal seeds, quotient-image saturation traps the orbit in the
penultimate kernel and makes its full terminal displacement vanish.
The source (3.3) bound then puts the normal orbit in B, forcing H to vanish.
Thus one terminal seed contains H, and H centralizes the entire endpoint
radius. No central attachment is removed and no complement is chosen.

This is the critical-pair exclusion needed in the central-H branch of
Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two (1993),
(5.9), printed pp.920--921. The subsequent source conjugator, second span
comparison, strict index and distance-two existence remain separate steps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit h [Finite H] in
private theorem two_step_edges
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 2 ≤ geometry.b d.radical) :
    Adjacent d.radical a (path.walk.getVert 1) ∧
      Adjacent d.radical (path.walk.getVert 2) (path.walk.getVert 1) := by
  have hlen : 2 ≤ path.walk.length := by rwa [path.length_eq_b]
  constructor
  · have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  · exact adjacent_symm _ ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))

/-- The full vertex orbit has exactly H as its T₀-displacement. -/
theorem Input.replacement_strict_index_central_span_displacement
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F) :
    let c := path.walk.getVert 2
    let W := sourceSeedSpan d.radical c a
    Z d.radical c ≤ W ∧ Z d.radical a ≤ W ∧ W ≤ V d.radical a ∧
      stabilizer d.radical a ≤ normalizer (W : Set _) ∧
      ⁅W,kernelCentralizer geometry a c⁆ = kernelCommutator geometry a c := by
  dsimp only
  obtain ⟨hat,hct⟩ := two_step_edges d path (by omega)
  have hc : color d.radical (path.walk.getVert 2)=false :=
    (path.vertex_color (by rw [path.length_eq_b]; omega)).mpr (by decide)
  have hZV := le_sup_left.trans (neighbor_seed_join_le_radius hat hct)
  have hZQ := hZV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hcent := h.replacement_strict_index_kernel_central d path hb hsmall
  refine ⟨le_conjugateSpanBy _ _,
    local_seed_le_conjugateSpan_of_common_neighbor hc path.start_color hct hat,
    conjugateSpanBy_le hZV (DistanceEight.V_normalized d.radical a),
    le_normalizer_conjugateSpanBy _ _,?_⟩
  change ⁅conjugateSpanBy _ _,_⁆ = _
  rw [commutator_conjugateSpanBy_of_normalized_right _ _ _
    (hZQ.trans (fun _ hx => hx.1))
    (kernelCentralizer_normalized_at_edge geometry (by omega)
      (h.replacement_residual_edge_generation d) path.start_color hat hct),
    h.replacement_kernel_full_seed_commutator d geometry hb.le path.start_color hat hct]
  exact le_antisymm (conjugateSpanBy_le le_rfl
    ((le_centralizer_iff.mp hcent).trans (Subgroup.centralizer_le_normalizer _)))
    (le_conjugateSpanBy _ _)

/-- Centrality keeps H unchanged at every conjugate seed of the full orbit. -/
private theorem central_kernel_conjugate
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (k : FreeAmalgam d.radical) (hk : k ∈ stabilizer d.radical a) :
    kernelCommutator geometry a (act d.radical k (path.walk.getVert 2)) =
      kernelCommutator geometry a (path.walk.getVert 2) := by
  obtain ⟨hat,hct⟩ := two_step_edges d path (by omega)
  rw [(h.replacement_kernel_conjugate_at_edge d geometry (by omega)
    path.start_color hat hct k hk).2]
  exact mem_normalizer_iff_map_conj_eq.mp
    (((le_centralizer_iff.mp (h.replacement_strict_index_kernel_central d path hb hsmall)).trans
      (Subgroup.centralizer_le_normalizer _)) ((stabilizer d.radical a).inv_mem hk))

/-- If H escapes the penultimate seed, every seed in the full vertex orbit is in its kernel. -/
theorem Input.replacement_central_span_le_penultimate_kernel
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (hescape : ¬ kernelCommutator geometry a (path.walk.getVert 2) ≤
      Z d.radical (path.walk.getVert (path.walk.length-2))) :
    sourceSeedSpan d.radical (path.walk.getVert 2) a ≤
      Q d.radical (path.walk.getVert (path.walk.length-2)) := by
  obtain ⟨hat,hct⟩ := two_step_edges d path (by omega)
  obtain ⟨_,_,htail,_,_⟩ := h.replacement_strict_index_kernel_at_two_step d path hb hsmall
  apply (closure_le _).mpr
  rintro _ ⟨k,hk,u,hu,rfl⟩
  let c' := act d.radical k⁻¹ (path.walk.getVert 2)
  let t' := act d.radical k⁻¹ (path.walk.getVert 1)
  have hkfix : act d.radical k⁻¹ a=a := (stabilizer d.radical a).inv_mem hk
  have hat' : Adjacent d.radical a t' := by
    have hh := (adjacent_act_iff d.radical k⁻¹ a _).mpr hat
    rwa [hkfix] at hh
  have hct' : Adjacent d.radical c' t' := (adjacent_act_iff d.radical k⁻¹ _ _).mpr hct
  have hT := (h.replacement_kernel_conjugate_at_edge d geometry (by omega)
    path.start_color hat hct k⁻¹ ((stabilizer d.radical a).inv_mem hk)).1
  have hH := central_kernel_conjugate h d path hb hsmall k⁻¹ ((stabilizer d.radical a).inv_mem hk)
  have hsmall' : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c') ≤ Nat.card F := by
    rw [movingIndex_act geometry (by omega) path.start_color k⁻¹
      ((stabilizer d.radical a).inv_mem hk)]
    exact hsmall
  have htrap : Z d.radical c' ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
    by_contra hn
    obtain ⟨back,_,_⟩ := exists_backward_path_of_not_le geometry (by omega) path hat' hct' hn
    have he := h.replacement_kernel_critical_seed_saturation d back hb.le path.start_color
      hat' hct' hsmall' (by rw [hT]; exact le_sup_left.trans htail)
    rw [hH] at he
    apply hescape
    rw [he]
    exact le_normalizer_iff_commutator_le_right.mp
      ((Z_le_stabilizer_of_dist_le c' (geometry.exists_critical c' back.start_color)
        back.critical.1.le).trans (Z_normalized d.radical _))
  apply htrap
  rw [Z_act]
  exact ⟨u,hu,by simp only [inv_inv]; rfl⟩

/-- A nonzero intersection displacement would put the same full H in the endpoint seed. -/
theorem Input.replacement_central_span_terminal_centralizes
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (hpescape : ¬ kernelCommutator geometry a (path.walk.getVert 2) ≤
      Z d.radical (path.walk.getVert (path.walk.length-2)))
    (hzescape : ¬ kernelCommutator geometry a (path.walk.getVert 2) ≤ Z d.radical z) :
    let W := sourceSeedSpan d.radical (path.walk.getVert 2) a
    W ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
      ⁅W,Z d.radical (path.walk.getVert (path.walk.length-2)) ⊔
        (Z d.radical z ⊓ Q d.radical a)⁆=⊥ := by
  dsimp only
  let p := path.walk.getVert (path.walk.length-2)
  let W := sourceSeedSpan d.radical (path.walk.getVert 2) a
  let A := Z d.radical z ⊓ Q d.radical a
  obtain ⟨hat,hct⟩ := two_step_edges d path (by omega)
  obtain ⟨_,_,htail,_,_⟩ := h.replacement_strict_index_kernel_at_two_step d path hb hsmall
  have hWQ := h.replacement_central_span_le_penultimate_kernel d path hb hsmall hpescape
  have hp : color d.radical p=false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    have he : Even path.walk.length := by
      rw [path.length_eq_b]
      exact geometry.even (alpha d.radical) rfl
    rw [Nat.even_iff] at he ⊢
    omega
  have hpz : (cosetGraph d.radical).dist p z=2 := by
    rw [path.dist_end]
    have hlen : 2 ≤ path.walk.length := by rw [path.length_eq_b]; omega
    omega
  have hWz : W ≤ stabilizer d.radical z := hWQ.trans
    (Q_le_stabilizer_of_dist_le_two p z hp path.end_color hpz.le)
  have hWA : W ≤ centralizer (A : Set (FreeAmalgam d.radical)) := by
    apply (closure_le _).mpr
    rintro _ ⟨k,hk,u,hu,rfl⟩
    let c' := act d.radical k⁻¹ (path.walk.getVert 2)
    let t' := act d.radical k⁻¹ (path.walk.getVert 1)
    have hkfix : act d.radical k⁻¹ a=a := (stabilizer d.radical a).inv_mem hk
    have hat' : Adjacent d.radical a t' := by
      have hh := (adjacent_act_iff d.radical k⁻¹ a _).mpr hat
      rwa [hkfix] at hh
    have hct' : Adjacent d.radical c' t' := (adjacent_act_iff d.radical k⁻¹ _ _).mpr hct
    have ht' : color d.radical t'=true := by
      have hh := adjacent_color_ne d.radical hat'
      rw [path.start_color] at hh
      cases ht' : color d.radical t' <;> simp_all
    have hc' : color d.radical c'=false := by
      have hh := adjacent_color_ne d.radical hct'
      rw [ht'] at hh
      cases hc' : color d.radical c' <;> simp_all
    have hT := (h.replacement_kernel_conjugate_at_edge d geometry (by omega)
      path.start_color hat hct k⁻¹ ((stabilizer d.radical a).inv_mem hk)).1
    have hH := central_kernel_conjugate h d path hb hsmall k⁻¹ ((stabilizer d.radical a).inv_mem hk)
    have hsmall' : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c') ≤ Nat.card F := by
      rw [movingIndex_act geometry (by omega) path.start_color k⁻¹
        ((stabilizer d.radical a).inv_mem hk)]
      exact hsmall
    have hseed : Z d.radical c' ≤ W := by
      rw [Z_act]
      rintro _ ⟨v,hv,rfl⟩
      apply Subgroup.subset_closure
      exact ⟨k,hk,v,hv,by simp only [inv_inv]; rfl⟩
    have hTS : kernelCentralizer geometry a c' ≤ stabilizer d.radical c' :=
      inf_le_left.trans ((Q_le_adjacent_h d.radical ht' hat').trans
        (fun _ hv => hv.2 c' (adjacent_symm d.radical hct')))
    have hAT : A ≤ kernelCentralizer geometry a c' := by rw [hT]; exact le_sup_right.trans htail
    have hAS := hAT.trans hTS
    have hzero : ⁅Z d.radical c',A⁆=⊥ := by
      by_contra hn
      have hlo := h.replacement_critical_intersection_moving_index_lower d path hb.le
        (Z d.radical c') (hseed.trans hWz) hn
      have hC := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
        (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) c' hc'
      have hidx : (centralizer (Z d.radical c' : Set (FreeAmalgam d.radical))).relIndex A=
          (Q d.radical c').relIndex A := by
        rw [←hC]
        change ((centralizer (Z d.radical c' : Set (FreeAmalgam d.radical))).subgroupOf A).index=
          ((stabilizer d.radical c' ⊓ centralizer (Z d.radical c' : Set (FreeAmalgam d.radical))).subgroupOf A).index
        congr 1
        ext v
        exact ⟨fun hv => ⟨hAS v.property,hv⟩,fun hv => hv.2⟩
      rw [hidx] at hlo
      have he := (h.replacement_field_index_actor_saturates d geometry hb.le hc' A
        (kernelCentralizer geometry a c') hAT hTS
        ((kernelCentralizer_moving_index_le geometry a c').trans hsmall') hlo).2
      rw [h.replacement_kernel_full_seed_commutator d geometry hb.le path.start_color hat' hct',hH] at he
      apply hzescape
      rw [←he,commutator_comm]
      exact (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp ((hseed.trans hWz).trans (Z_normalized d.radical z)))
    apply (commutator_eq_bot_iff_le_centralizer.mp hzero)
    rw [Z_act]
    exact ⟨u,hu,by simp only [inv_inv]; rfl⟩
  refine ⟨hWQ,commutator_eq_bot_iff_le_centralizer.mpr ?_⟩
  exact le_centralizer_iff.mpr (sup_le
    ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes p hp)).trans
      (centralizer_le hWQ)) (le_centralizer_iff.mp hWA))

/-- At least one terminal seed contains the complete H. -/
theorem Input.replacement_strict_index_kernel_terminal_alternative
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F) :
    kernelCommutator geometry a (path.walk.getVert 2) ≤
      Z d.radical (path.walk.getVert (path.walk.length-2)) ∨
    kernelCommutator geometry a (path.walk.getVert 2) ≤ Z d.radical z := by
  by_contra! hbad
  obtain ⟨hZc,_,hWV,hn,_⟩ := h.replacement_strict_index_central_span_displacement d path hb hsmall
  obtain ⟨hWQ,hzero⟩ := h.replacement_central_span_terminal_centralizes d path hb hsmall hbad.1 hbad.2
  let W := sourceSeedSpan d.radical (path.walk.getVert 2) a
  have hWz : W ≤ stabilizer d.radical z :=
    (le_inf hWV hWQ).trans (CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.truncated_radius_le_endpoint_stabilizer path (by omega))
  have hWQa : W ≤ Q d.radical a := hWV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hWfix : W ≤ centralizer ((Z d.radical z ⊓ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) :=
    (commutator_eq_bot_iff_le_centralizer.mp hzero).trans (centralizer_le (fun _ hx => mem_sup_right hx))
  have hWend : ⁅W,Z d.radical z⁆ ≤ Z d.radical a := by
    rw [commutator_comm]
    exact (h.replacement_critical_fixed_intersection_displacement d path (by omega)
      W hWz hWQa hWfix).trans (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path)
  obtain ⟨E,hE,f,hf,hfQ,_⟩ := h.replacement_inner_natural_action d geometry hb.le path.start_color
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Sp E.Carrier) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  have hk : f.ker=(Q d.radical a).subgroupOf (stabilizer d.radical a) := by
    apply map_injective (stabilizer d.radical a).subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ stabilizer d.radical a from fun _ hv => hv.1)]
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  have hzQ := (critical_reverse d.radical geometry hedge a path.start_color
    (by rw [geometry.distance_constant a path.start_color]; change 0 < geometry.b d.radical; omega)
    z path.end_color path.critical).2
  have hWB := normal_radius_le_B_of_kernel_escape geometry (by omega) path.start_color f hf hk
    (Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d) a path.start_color)
    W (Z d.radical z) hWV hn hzS hzQ hWend
  have hUB : U d.radical (path.walk.getVert 2) ≤ B d.radical a (geometry.Z_normal a) :=
    (U_le_Z _).trans (hZc.trans hWB)
  have hHbot : kernelCommutator geometry a (path.walk.getVert 2)=⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    change Q d.radical a ⊓ centralizer ((U d.radical (path.walk.getVert 2) ⊓
      B d.radical a (geometry.Z_normal a) : Subgroup _) : Set _) ≤ _
    rw [inf_eq_left.mpr hUB]
    exact inf_le_right
  exact hbad.2 (hHbot ▸ bot_le)

/-- In the surviving central branch H fixes the complete endpoint radius. -/
theorem Input.replacement_strict_index_kernel_centralizes_endpoint_radius
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F) :
    kernelCommutator geometry a (path.walk.getVert 2) ≤
      centralizer (V d.radical z : Set (FreeAmalgam d.radical)) := by
  rcases h.replacement_strict_index_kernel_terminal_alternative d path hb hsmall with hp | hz
  · have hpcol : color d.radical (path.walk.getVert (path.walk.length-2))=false := by
      apply (path.vertex_color (Nat.sub_le _ _)).mpr
      have he : Even path.walk.length := by
        rw [path.length_eq_b]
        exact geometry.even (alpha d.radical) rfl
      rw [Nat.even_iff] at he ⊢
      omega
    have hVQ : V d.radical z ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
      apply V_le_Q_of_dist_add_two_lt d.radical path.end_color
      rw [SimpleGraph.dist_comm,path.dist_end]
      have hlen : 2 ≤ path.walk.length := by rw [path.length_eq_b]; omega
      change path.walk.length-(path.walk.length-2)+2 < geometry.b d.radical
      omega
    exact hp.trans ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes _ hpcol)).trans
      (centralizer_le hVQ))
  · exact hz.trans ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color)).trans
      (centralizer_le (geometry.V_le_Q (by omega) z path.end_color)))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
