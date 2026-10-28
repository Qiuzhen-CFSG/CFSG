module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexExclusion
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.OriginalLargePaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.LargeDistance.Centers

/-!
# Prescribed terminal paths and the large-mover central intersection

MS93 (5.9) makes the seed join at the actual first two-step vertex
nonnormal: the critical endpoint fixes that neighbor, and simplicity would
otherwise put the whole normal join in B. Thus the established root and
large-image selectors can shift this prescribed neighbor at every step.
Iteration retains both initial vertices in one residual orbit, the literal
full-B index, every overlap, and equality or inequality of the original
neighboring movers at every newly covered position.

In the full point-mover branch, edge transitivity preserves that branch.
The same choices also retain generation by each individual smaller mover
and the full original-edge fixed subgroup. These source generations now
put the entire R₄ edge intersection in the three literal full vertex
centers. No central attachment, quotient kernel or original field degree
is removed.

The general orbit sequence records only the orbit and index part of the
selection; it does not assert all Lambda clauses in the unequal contained
branch. The complete unequal-mover terminal selection, subsequent order
comparisons, MS93 (5.10)--(5.12) exclusions and the minimum-replacement
distance-two witness remain to be proved. Original-radical characteristic
control remains a separate obligation.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.7), (5.9), and the opening of (5.10), printed pp.919--923.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The join at the literal first two-step vertex is not vertex-normal.
The endpoint centralizes that neighbor, so normality would force the join
into the full B-preimage and contradict the strict moving index. -/
theorem Input.replacement_path_neighbor_join_not_normal
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical) :
    ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical (path.walk.getVert 2) ⊔ Z d.radical a :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  intro hn
  let c := path.walk.getVert 2
  let Y := Z d.radical c ⊔ Z d.radical a
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hc : color d.radical c=false :=
    (path.vertex_color (by omega)).mpr (by decide)
  have hcz : Z d.radical c ≤ Q d.radical z := by
    apply Z_le_Q_of_dist_lt d.radical c (geometry.exists_critical c hc)
    rw [geometry.distance_constant c hc,path.dist_end,path.length_eq_b]
    change geometry.b d.radical-2 < geometry.b d.radical
    omega
  have hfix : ⁅Z d.radical c,Z d.radical z⁆=⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hcz.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color)))
  have hYV : Y ≤ V d.radical a := by
    apply sup_le
    · exact le_iSup_of_le c (le_iSup_of_le (by
        rw [SimpleGraph.dist_comm]
        exact (path.dist_start (by omega : 2 ≤ path.walk.length)).le) le_rfl)
    · exact Z_le_VBall d.radical a 2
  have hYS := (hYV.trans (geometry.V_le_Q (by omega) a path.start_color)).trans
    (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1)
  have hdisp : ⁅Y,Z d.radical z⁆ ≤ Z d.radical a := by
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      (Z d.radical c) (Z d.radical a) (Z d.radical z) (Z d.radical a)
      (Z_normalized d.radical a)
      (le_sup_left.trans hYS) (Z_le_stabilizer d.radical a)
    · rw [hfix]; exact bot_le
    · exact le_normalizer_iff_commutator_le_left.mp
        ((path.endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized d.radical a))
  obtain ⟨E,hE,f,hf,hfQ,_⟩ := h.replacement_inner_natural_action d geometry hb.le path.start_color
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Sp E.Carrier) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  have hk : f.ker=(Q d.radical a).subgroupOf (stabilizer d.radical a) := by
    apply map_injective (stabilizer d.radical a).subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1)]
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  have hescape := (critical_reverse d.radical geometry hedge a path.start_color
    (by rw [geometry.distance_constant a path.start_color]; exact lt_trans (by decide) hb)
    z path.end_color path.critical).2
  have hYB := normal_radius_le_B_of_kernel_escape geometry (by omega) path.start_color
    f hf hk (Q_isPGroup d.radical (h.replacement_two_group d)
      (h.replacement_core_le d) a path.start_color)
    Y (Z d.radical z) hYV hn (path.endpoint_Z_le_start_stabilizer (by omega)) hescape hdisp
  have hone := relIndex_eq_one.mpr (((U_le_Z c).trans le_sup_left).trans hYB)
  have hstrict := h.replacement_path_moving_index_gt_field d path hb
  rw [hone] at hstrict
  have hq : 1 < Nat.card F := Finite.one_lt_card
  omega

/-- The backward shift uses the literal two-step vertex of the original
critical path, in both critical-image branches. -/
theorem Input.replacement_prescribed_path_backward_step
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical) :
    ∃ y ∈ Ltilde d.radical a,
      let v := act d.radical y (path.walk.getVert 2)
      let w := act d.radical y (path.walk.getVert 1)
      Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
      (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) =
        (B d.radical a (geometry.Z_normal a)).relIndex
          (U d.radical (path.walk.getVert 2)) ∧
      ∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = w ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i := by
  let t := path.walk.getVert 1
  let c := path.walk.getVert 2
  have hat : Adjacent d.radical a t := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 1 < path.walk.length)))
  by_cases hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z)
  · have hnormal := h.replacement_path_neighbor_join_not_normal d path hb
    by_cases hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
          (U d.radical a) ≤ Nat.card F^2
    · obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax⟩ :=
        h.replacement_maximizing_parabolic d geometry hb.le path.start_color hat
      have hJplane := h.replacement_small_mover_le_maximizing_plane_of_index_le d
        geometry hb.le path.start_color hat E hE f hfQ hTf hindex hmax hJm
      obtain ⟨g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,hgen₁,hgen₂,hfixed,hxn,hxp,
        v,hv,w,hvw,haw,hvw',hn,hidx,hback⟩ :=
        h.replacement_original_smaller_large_backward_path d path hb.le hat rfl hct hnormal
          E hE f hf hfQ hTf hindex hlarge hJplane
      rcases hvw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨g⁻¹,(Ltilde d.radical a).inv_mem hg,haw,hvw',hidx,hback⟩
      · refine ⟨g⁻¹*x,(Ltilde d.radical a).mul_mem ((Ltilde d.radical a).inv_mem hg) hx,?_⟩
        dsimp only
        rw [act_mul,act_mul]
        exact ⟨haw,hvw',hidx,hback⟩
    · have hq : 1 < Nat.card F := Finite.one_lt_card
      have hl : Nat.card F < (Q d.radical a).relIndex (Z d.radical z) := by nlinarith
      obtain ⟨g,hg,haw,hvw,hidx,htransport,hgen,hfixed,hn,hback⟩ :=
        h.replacement_large_movement_selected_large_at_neighbor d path hb.le hat rfl hct
          hnormal hl (lt_of_not_ge hJm)
      exact ⟨g⁻¹,(Ltilde d.radical a).inv_mem hg,haw,hvw,hidx,hback⟩
  · exact h.replacement_root_backward_step d path hb.le hat rfl hct
      (h.replacement_path_moving_index_gt_field d path hb) (lt_of_not_ge hlarge)

/-- The literal choice used to iterate terminal paths. It retains the
residual transporter of both initial vertices and the exact full-B index. -/
@[expose] def pathOrbitChoice {M : Type*} [Group M] {R : Subgroup M}
    (geometry : Geometry R) (p : CriticalSegment geometry) (v w : Vertex R) : Prop :=
  ∃ y ∈ Ltilde R p.first,
    v = act R y (p.path.walk.getVert 2) ∧
    w = act R y (p.path.walk.getVert 1) ∧
    (B R p.first (geometry.Z_normal p.first)).relIndex (U R v) = nextMovingIndex p

/-- The same original path now has arbitrarily many backward shifts in the
prescribed residual orbits. No selected-path or strict-index premise remains. -/
theorem Input.replacement_terminal_path_sequence
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical) :
    ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
      (∀ i, BackwardLink geometry (pathOrbitChoice geometry) (s i) (s (i+1))) ∧
      (∀ i k j, j+2*k ≤ geometry.b d.radical →
        (s (i+k)).path.walk.getVert (j+2*k) = (s i).path.walk.getVert j) ∧
      (∀ i, Nat.card F < nextMovingIndex (s i)) ∧
      (∀ i, ∃ y ∈ Ltilde d.radical (s (i+1)).first,
        act d.radical y (s i).first = (s (i+2)).first) ∧
      (∀ i, ⁅Z d.radical (s (i+2)).first,Z d.radical (s (i+2)).last⁆ ≤
        centralizer ((Z d.radical (s i).last ⊔ Z d.radical (s (i+1)).last :
          Subgroup (FreeAmalgam d.radical)) : Set _)) := by
  have hstep (q : CriticalSegment geometry) :
      ∃ v t, pathOrbitChoice geometry q v t ∧ Adjacent d.radical q.first t ∧
        Adjacent d.radical v t ∧
        ¬ Z d.radical v ≤ Q d.radical (q.path.walk.getVert (geometry.b d.radical-2)) := by
    obtain ⟨y,hy,haw,hvw,hidx,back,hfirst,hover⟩ :=
      h.replacement_prescribed_path_backward_step d q.path hb
    refine ⟨act d.radical y (q.path.walk.getVert 2),
      act d.radical y (q.path.walk.getVert 1),⟨y,hy,rfl,rfl,hidx⟩,haw,hvw,?_⟩
    simpa only [q.path.length_eq_b] using back.critical.2
  obtain ⟨s,hs0,hs,hover⟩ := exists_chosen_sequence (by omega)
    (pathOrbitChoice geometry) hstep p
  refine ⟨s,hs0,hs,hover,?_,?_,?_⟩
  · intro i
    exact h.replacement_path_moving_index_gt_field d (s i).path hb
  · intro i
    obtain ⟨t,⟨y,hy,hyv,hyt,hidx⟩,_,_,_⟩ := (hs (i+1)).choice
    have he := (hs i).overlap 0 (by omega)
    simp only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] at he
    rw [he] at hyv
    exact ⟨y,hy,hyv.symm⟩
  · intro i
    apply le_centralizer_iff.mp
    apply sup_le
    · exact le_centralizer_iff.mp
        (shifted_commutator_centralizes_endpoint (pathOrbitChoice geometry) s hs i 2 (by omega))
    · exact le_centralizer_iff.mp
        (shifted_commutator_centralizes_endpoint (pathOrbitChoice geometry) s hs (i+1) 1 (by omega))

omit h in
private theorem mover_index_act {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (q : ℕ) (g : FreeAmalgam R) (a t : Vertex R) :
    (centralizer (Subgroup.SmallMover.join (U R (act R g a)) (Q R (act R g a))
      (Q R (act R g t)) (q^2) : Set (FreeAmalgam R))).relIndex (U R (act R g a)) =
    (centralizer (Subgroup.SmallMover.join (U R a) (Q R a)
      (Q R t) (q^2) : Set (FreeAmalgam R))).relIndex (U R a) := by
  rw [U_act,Q_act,Q_act,←Subgroup.SmallMover.join_map _ (MulAut.conj g⁻¹).injective,
    coe_map,MulEquiv.coe_toMonoidHom,←Theory.GroupTheory.map_centralizer_equiv]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective

omit h in
private theorem mover_index_eq_of_edges {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (q : ℕ) {a t c w : Vertex R} (ha : color R a=false) (hc : color R c=false)
    (hat : Adjacent R a t) (hcw : Adjacent R c w) :
    (centralizer (Subgroup.SmallMover.join (U R c) (Q R c)
      (Q R w) (q^2) : Set (FreeAmalgam R))).relIndex (U R c) =
    (centralizer (Subgroup.SmallMover.join (U R a) (Q R a)
      (Q R t) (q^2) : Set (FreeAmalgam R))).relIndex (U R a) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color R hc
  obtain ⟨j,hj⟩ := exists_mVertex_of_color R ha
  let y := g⁻¹*j
  have hy : act R y c=a := by
    rw [hg,act_mVertex]
    dsimp [y]
    rw [mul_inv_cancel_left,←hj]
  have had : Adjacent R a (act R y w) := by
    rw [←hy]
    exact (adjacent_act_iff R y _ _).mpr hcw
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors R a had hat
  have hka : act R (y*x) c=a := by rw [act_mul,hy]; exact hx
  have hkt : act R (y*x) w=t := by rw [act_mul,hxt]
  have hh := mover_index_act q (y*x) c w
  rw [hka,hkt] at hh
  exact hh.symm

/-- In the large-mover branch the same selected neighbor retains individual
mover generation and the full original-edge fixed subgroup. -/
@[expose] def pointPathChoice {M : Type*} [Group M] {R : Subgroup M}
    (geometry : Geometry R) (q : ℕ) (p : CriticalSegment geometry) (v w : Vertex R) : Prop :=
  pathOrbitChoice geometry p v w ∧
    Subgroup.SmallMover.join (U R v) (Q R v) (Q R w) (q^2) ⊔ Z R p.last =
      stabilizer R p.first ∧
    Z R (p.path.walk.getVert 1) ⊓ centralizer
      (Subgroup.SmallMover.join (U R v) (Q R v) (Q R w) (q^2) : Set (FreeAmalgam R)) =
    Z R (p.path.walk.getVert 1) ⊓ centralizer (stabilizer R p.first : Set (FreeAmalgam R))

/-- The actual large-mover source choice discharges all generation premises
in the three-center propagation for R₄ in the opening of MS93 (5.10). -/
theorem Input.replacement_large_mover_terminal_centers
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical)
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical p.first)
      (Q d.radical p.first) (Q d.radical (p.path.walk.getVert 1)) (Nat.card F^2) :
        Set (FreeAmalgam d.radical))).relIndex (U d.radical p.first)) :
    ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
      (∀ i, BackwardLink geometry (pointPathChoice geometry (Nat.card F)) (s i) (s (i+1))) ∧
      (∀ i k j, j+2*k ≤ geometry.b d.radical →
        (s (i+k)).path.walk.getVert (j+2*k) = (s i).path.walk.getVert j) ∧
      (∀ i, ⁅Z d.radical (s (i+2)).first,Z d.radical (s (i+2)).last⁆ ⊓
          Z d.radical ((s (i+2)).path.walk.getVert 1) ≤
        (stabilizer d.radical (s (i+1)).first ⊓
          centralizer (stabilizer d.radical (s (i+1)).first : Set (FreeAmalgam d.radical))) ⊓
        (stabilizer d.radical (s i).first ⊓
          centralizer (stabilizer d.radical (s i).first : Set (FreeAmalgam d.radical))) ⊓
        (stabilizer d.radical (s (i+2)).first ⊓
          centralizer (stabilizer d.radical (s (i+2)).first : Set (FreeAmalgam d.radical)))) := by
  have first_adj (q : CriticalSegment geometry) :
      Adjacent d.radical q.first (q.path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (q.path.walk.adj_getVert_succ (by rw [q.path.length_eq_b]; omega : 0 < q.path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hstep (q : CriticalSegment geometry) :
      ∃ v t, pointPathChoice geometry (Nat.card F) q v t ∧
        Adjacent d.radical q.first t ∧ Adjacent d.radical v t ∧
        ¬ Z d.radical v ≤ Q d.radical (q.path.walk.getVert (geometry.b d.radical-2)) := by
    let t := q.path.walk.getVert 1
    let c := q.path.walk.getVert 2
    have hat := first_adj q
    have hct : Adjacent d.radical c t := adjacent_symm d.radical
      ((cosetGraph_adj d.radical _ _).mp
        (q.path.walk.adj_getVert_succ (by rw [q.path.length_eq_b]; omega : 1 < q.path.walk.length)))
    have hJq : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical q.first)
        (Q d.radical q.first) (Q d.radical t) (Nat.card F^2) :
          Set (FreeAmalgam d.radical))).relIndex (U d.radical q.first) := by
      rw [mover_index_eq_of_edges (Nat.card F) p.path.start_color q.path.start_color (first_adj p) hat]
      exact hJm
    have hchoice : ∃ g ∈ Ltilde d.radical q.first,
        let w := act d.radical g⁻¹ t
        let v := act d.radical g⁻¹ c
        let J := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
          (Q d.radical t) (Nat.card F^2)
        Adjacent d.radical q.first w ∧ Adjacent d.radical v w ∧
        (B d.radical q.first (geometry.Z_normal q.first)).relIndex (U d.radical v) =
          (B d.radical q.first (geometry.Z_normal q.first)).relIndex (U d.radical c) ∧
        J.map (MulAut.conj g).toMonoidHom = Subgroup.SmallMover.join
          (U d.radical v) (Q d.radical v) (Q d.radical w) (Nat.card F^2) ∧
        J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical q.last = stabilizer d.radical q.first ∧
        Z d.radical t ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical)) =
          Z d.radical t ⊓ centralizer (stabilizer d.radical q.first : Set (FreeAmalgam d.radical)) ∧
        ¬ Z d.radical q.last ≤ normalizer
          ((Z d.radical v ⊔ Z d.radical q.first : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        (∃ back : CriticalPath d.radical geometry v (q.path.walk.getVert (q.path.walk.length-2)),
          back.walk.getVert 1 = w ∧
          ∀ i ≤ q.path.walk.length-2, back.walk.getVert (i+2) = q.path.walk.getVert i) := by
      by_cases hsmall : (Q d.radical q.first).relIndex (Z d.radical q.last) < Nat.card F^2
      · exact h.replacement_large_movement_root_backward_path d q.path hb.le hat rfl hct
          (h.replacement_path_moving_index_gt_field d q.path hb) hsmall hJq
      · have hq : 1 < Nat.card F := Finite.one_lt_card
        exact h.replacement_large_movement_selected_large_at_neighbor d q.path hb.le hat rfl hct
          (h.replacement_path_neighbor_join_not_normal d q.path hb) (by nlinarith) hJq
    obtain ⟨g,hg,haw,hvw,hidx,htransport,hgen,hfixed,hn,back,hfirst,hover⟩ := hchoice
    rw [htransport] at hgen hfixed
    refine ⟨act d.radical g⁻¹ c,act d.radical g⁻¹ t,
      ⟨⟨g⁻¹,(Ltilde d.radical q.first).inv_mem hg,rfl,rfl,hidx⟩,hgen,hfixed⟩,haw,hvw,?_⟩
    simpa only [q.path.length_eq_b] using back.critical.2
  obtain ⟨s,hs0,hs,hover⟩ := exists_chosen_sequence (by omega)
    (pointPathChoice geometry (Nat.card F)) hstep p
  refine ⟨s,hs0,hs,hover,?_⟩
  intro i
  obtain ⟨v,hv,hav,hcv,hfirst₁⟩ := (hs i).choice
  obtain ⟨t,ht,hct,hat,hfirst₂⟩ := (hs (i+1)).choice
  obtain ⟨y,hy,hyv,hyt,hidx⟩ := ht.1
  have he := (hs i).overlap 0 (by omega)
  simp only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] at he
  rw [he] at hyv
  have htcol : color d.radical t=true := by
    have hn := adjacent_color_ne d.radical hct
    rw [(s (i+1)).path.start_color] at hn
    cases hh : color d.radical t <;> simp_all
  have hgenC : stabilizer d.radical (s (i+1)).first ≤ Q d.radical t ⊔ Z d.radical (s (i+1)).last := by
    rw [←ht.2.1]
    exact sup_le_sup_right (Subgroup.SmallMover.join_le _ _ _ _) _
  have hgenD : stabilizer d.radical (s i).first ≤ Q d.radical v ⊔ Z d.radical (s i).last := by
    rw [←hv.2.1]
    exact sup_le_sup_right (Subgroup.SmallMover.join_le _ _ _ _) _
  rw [hfirst₂]
  exact fourth_shift_intersection_le_full_centers hb (pointPathChoice geometry (Nat.card F))
    (fun j => s (i+j)) (fun j => by simpa only [Nat.add_assoc] using hs (i+j))
    hct hcv htcol hgenC hgenD y (Ltilde_le_stabilizer _ hy) hyv.symm

/-- Equality of the literal neighboring movers at a specified even position;
the bound is the square of the original field order. -/
@[expose] def pathMoverAgreement {M : Type*} [Group M] {R : Subgroup M}
    {geometry : Geometry R} (q : ℕ) (p : CriticalSegment geometry) (k : ℕ) : Prop :=
  Subgroup.SmallMover.join (U R (p.path.walk.getVert (2*k+2)))
    (Q R (p.path.walk.getVert (2*k+2))) (Q R (p.path.walk.getVert (2*k+1))) (q^2) =
  Subgroup.SmallMover.join (U R (p.path.walk.getVert (2*k)))
    (Q R (p.path.walk.getVert (2*k))) (Q R (p.path.walk.getVert (2*k+1))) (q^2)

omit h in
private theorem backward_path_mover_agreement {M : Type*} [Group M] [Finite M]
    {R : Subgroup M} {geometry : Geometry R} (q : ℕ) (hb : 2 ≤ geometry.b R)
    {p p' : CriticalSegment geometry} (hl : BackwardLink geometry (pathOrbitChoice geometry) p p') :
    pathMoverAgreement q p' 0 ↔ pathMoverAgreement q p 0 := by
  obtain ⟨t,⟨g,hg,hd,ht,_⟩,_,_,hqt⟩ := hl.choice
  have hga : act R g p.first=p.first := Ltilde_le_stabilizer _ hg
  have htwo : p'.path.walk.getVert 2=p.first := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hl.overlap 0 hb
  have hmap (a t : Vertex R) :
      Subgroup.SmallMover.join (U R (act R g a)) (Q R (act R g a))
        (Q R (act R g t)) (q^2) =
      (Subgroup.SmallMover.join (U R a) (Q R a) (Q R t) (q^2)).map
        (MulAut.conj g⁻¹).toMonoidHom := by
    rw [U_act,Q_act,Q_act,Subgroup.SmallMover.join_map _ (MulAut.conj g⁻¹).injective]
  have hJa := hmap p.first (p.path.walk.getVert 1)
  rw [hga] at hJa
  simp only [pathMoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero]
  rw [htwo,hqt,ht,hd,hJa,hmap]
  exact ⟨fun he => (Subgroup.map_injective (MulAut.conj g⁻¹).injective he).symm,
    fun he => congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) he.symm⟩

/-- The actual path construction propagates the original equal/unequal-mover
branch through every newly covered two-step segment, at the original degree. -/
theorem Input.replacement_terminal_mover_comparisons
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical) :
    ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
      (∀ i, BackwardLink geometry (pathOrbitChoice geometry) (s i) (s (i+1))) ∧
      (∀ i k j, j+2*k ≤ geometry.b d.radical →
        (s (i+k)).path.walk.getVert (j+2*k) = (s i).path.walk.getVert j) ∧
      (∀ i k, 2*k+2 ≤ geometry.b d.radical →
        (pathMoverAgreement (Nat.card F) (s (i+k)) k ↔ pathMoverAgreement (Nat.card F) p 0)) := by
  obtain ⟨s,hs0,hs,hover,hidx,horbit,hcomm⟩ := h.replacement_terminal_path_sequence d p hb
  have hfirst (i : ℕ) : pathMoverAgreement (Nat.card F) (s i) 0 ↔ pathMoverAgreement (Nat.card F) p 0 := by
    induction i with
    | zero => rw [hs0]
    | succ i hi => exact (backward_path_mover_agreement (Nat.card F) (by omega) (hs i)).trans hi
  refine ⟨s,hs0,hs,hover,?_⟩
  intro i k hk
  have htwo := hover i k 2 (by omega)
  have hone := hover i k 1 (by omega)
  have hzero := hover i k 0 (by omega)
  simp only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] at hzero
  simp only [pathMoverAgreement]
  rw [show 2*k+2=2+2*k by omega,htwo,show 2*k+1=1+2*k by omega,hone,hzero]
  simpa only [pathMoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hfirst i

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
