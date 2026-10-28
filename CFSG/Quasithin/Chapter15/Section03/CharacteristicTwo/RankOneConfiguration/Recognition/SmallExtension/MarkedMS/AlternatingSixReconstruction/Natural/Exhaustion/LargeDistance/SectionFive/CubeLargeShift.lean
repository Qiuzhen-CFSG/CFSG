module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSpanCollapse

/-!
# Generating backward shifts in the original three-pair branch

Quadratic action of the three-pair radical puts the full commutator of
any critical pair in its first edge seed. Two successive generating
backward shifts are therefore impossible above distance four. Their second
critical commutator centralizes both the actual edge radical and the old
endpoint seed, which generate the intermediate stabilizer. The retained
transporter then contradicts critical noncentrality at its own endpoint.

For an original nonsylow radical, the checked image reduction supplies the
three-pair hypothesis. A generating backward shift must consequently have
critical image two: a large image would construct the forbidden second
shift. The large-image shift is transported to every original component
vertex, retaining the prescribed neighbor, the actual stabilizer conjugator,
the generating edge and every overlap vertex. Its full critical commutator
has order two and is centralized by the whole original stabilizer, whose
two generators are both accounted for.

The literal large-image consumer now has forward Baumann index exactly
two. On the same backward path the reverse slice has index greater than
two, by the established small-image strict-slice theorem. Thus this remaining
branch supplies an asymmetric pair of slices with a specified central
critical line. This does not yet exclude that configuration or prove the
unconditional strict slice. Terminal (5.10)--(5.12), original Sylow and
distance-four exclusions, and the final distance-two application remain.

Both moved-cover orders, central attachments, the original nonsylow radical
and all original graph/action maps are retained. No exceptional cubic graph
or full point-core equality is substituted for this replacement.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.7)--(5.11), printed pp.919--924. The overlap/transport argument
adapts the checked `ShiftChain` proof, replacing its full point-core premise
by the actual three-pair quadratic action from `CubeKernelEdges`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- Quadratic three-pair action places the entire critical commutator in
its first edge seed, including when the critical image has order four. -/
theorem cube_critical_commutator_le_first_seed
    (hc : DistanceTwo.CentralLayer d) (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical (p.walk.getVert 1) := by
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hZe : Z d.radical a' ≤ Q d.radical (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(replacementGeometry h d).distance_constant a' p.end_color]
    change p.walk.length-1 < replacementDistance h d
    have he : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  exact (commutator_mono le_rfl hZe).trans (cube_edge_seed_commutator_le s hc u hR p.start_color hat)

include s in
/-- On the original three-pair graph two successive generating shifts
contradict critical noncentrality. Both transporters and all overlap vertices
are those of the given shifts. -/
theorem cube_two_backward_shifts_false
    (hc : DistanceTwo.CentralLayer d) (hb : 4 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path) : False := by
  have hq2 : q.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have hyz : act d.radical r.transporter a = r.start := by
    simpa only [hq2] using r.start_eq
  have hlenP : p.walk.length = replacementDistance h d := p.length_eq_b
  have hlenQ : q.path.walk.length = replacementDistance h d := q.path.length_eq_b
  have hdist1 : (cosetGraph d.radical).dist (q.path.walk.getVert (q.path.walk.length-2))
      (p.walk.getVert (p.walk.length-2)) = 2 := by
    rw [q.path.dist_end]
    omega
  have hdist2 : (cosetGraph d.radical).dist (p.walk.getVert (p.walk.length-2)) a' = 2 := by
    rw [p.dist_end]
    omega
  have hdist : (cosetGraph d.radical).dist (q.path.walk.getVert (q.path.walk.length-2)) a' ≤ 4 := by
    have hh := (cosetGraph_connected d.radical).dist_triangle
      (u := q.path.walk.getVert (q.path.walk.length-2)) (v := p.walk.getVert (p.walk.length-2)) (w := a')
    omega
  let H := ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆
  have hHe : H ≤ Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) :=
    ((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)
  have hcent (w : Vertex d.radical) (hw : color d.radical w = false)
      (hdist : (cosetGraph d.radical).dist (q.path.walk.getVert (q.path.walk.length-2)) w < replacementDistance h d) :
      H ≤ centralizer (Z d.radical w : Set (FreeAmalgam d.radical)) := by
    apply (hHe.trans (Z_le_Q_of_dist_lt d.radical _
      ((replacementGeometry h d).exists_critical _ r.path.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical w hw)))
    rwa [(replacementGeometry h d).distance_constant _ r.path.end_color]
  have hnc := critical_commutator_not_central_at_shift_vertex s hc r.path
    q.start q.edge a a' (by rw [r.first]; exact r.adjacent_start)
    q.adjacent_shift q.generation (hcent _ p.end_color (by omega)) r.transporter r.transporter_mem hyz
  have hHt : H ≤ Z d.radical r.edge := by
    simpa only [r.first] using cube_critical_commutator_le_first_seed s hc u hR r.path
  have ht : color d.radical r.edge = true := by
    have hh := adjacent_color_ne d.radical r.adjacent_start
    rw [q.path.start_color] at hh
    cases he : color d.radical r.edge <;> simp_all
  have hHQ : H ≤ centralizer (Q d.radical r.edge : Set (FreeAmalgam d.radical)) := by
    intro x hx
    have hh := hHt hx
    rw [Z,if_neg (by simp [ht])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  apply hnc
  change H ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))
  apply le_centralizer_iff.mp
  rw [←r.generation]
  exact sup_le (le_centralizer_iff.mp hHQ)
    (le_centralizer_iff.mp (hcent _ q.path.end_color (by omega)))

include e hz hn in
private theorem nonsylow_large_backward_step_base
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ c t x, x ∈ stabilizer d.radical (alpha d.radical) ∧
      act d.radical x (p.walk.getVert 2) = c ∧
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hel := critical_forward_not_le_slice_of_escape s hc hb2
    (nonsylow_criticalEscape_knownSimple (e := e) (hz := hz) (hn := hn) hb hns) p
  obtain ⟨t,hat,hgen,x,hx,hxt,q,hqt,hover,_⟩ :=
    nonsylow_large_image_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn)
      hb2 hns p hlarge hdelta hel
  refine ⟨_,t,x,hx,rfl,hat,?_,hgen,q,hqt,hover⟩
  rw [←hxt]
  exact (adjacent_act_iff d.radical x _ _).mpr hdelta

include e hz hn in
/-- A large critical image supplies a generating backward shift at every
original component vertex, retaining the same transporter and walk. -/
theorem nonsylow_large_backward_step_at_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ c t x, x ∈ stabilizer d.radical a ∧
      act d.radical x (p.walk.getVert 2) = c ∧
      Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical a ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := nonsylow_large_backward_step_base (e := e) (hz := hz) (hn := hn) hb hns
    (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  obtain ⟨c,t,x,hx,hxc,hat,hct,hgen,q,hq1,hover⟩ := base (p.act g⁻¹) (by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge)
  change act d.radical x ((actWalk d.radical g⁻¹ p.walk).getVert 2) = c at hxc
  rw [actWalk_getVert] at hxc
  let y := g⁻¹*x*g
  have hy (v : Vertex d.radical) :
      act d.radical y v = act d.radical g (act d.radical x (act d.radical g⁻¹ v)) := by
    simp only [y,act_mul]
  have hcancel (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hqc : ∃ r : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g c)
      (act d.radical g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2))),
      r.walk.getVert 1 = act d.radical g t ∧
      ∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i := by
    refine ⟨q.act g,?_,?_⟩
    · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act d.radical g) hq1
    · intro i hi
      have he := congrArg (act d.radical g) (hover i (by
        simpa only [CriticalPath.act,actWalk_length] using hi))
      simpa only [CriticalPath.act,actWalk_getVert,hcancel] using he
  have hend : act d.radical g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2)) =
      p.walk.getVert (p.walk.length-2) := by
    change act d.radical g ((actWalk d.radical g⁻¹ p.walk).getVert
      ((actWalk d.radical g⁻¹ p.walk).length-2)) = _
    rw [actWalk_length,actWalk_getVert,hcancel]
  rw [hend] at hqc
  obtain ⟨r,hr1,hrover⟩ := hqc
  refine ⟨act d.radical g c,act d.radical g t,y,?_,?_,?_,?_,?_,r,hr1,hrover⟩
  · change act d.radical y a = a
    rw [hy,show act d.radical x (act d.radical g⁻¹ a) = act d.radical g⁻¹ a from hx,hcancel]
  · rw [hy,hxc]
  · simpa only [hcancel] using (adjacent_act_iff d.radical g _ _).mpr hat
  · exact (adjacent_act_iff d.radical g _ _).mpr hct
  · have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hcancel,hcancel] at he
    exact he


include e hz hn in
/-- A generating backward shift in the nonsylow branch must have critical
image two. Otherwise its own large-image shift gives the forbidden pair
of successive generating shifts. -/
theorem nonsylow_generating_backward_shift_indices_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) :
    (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical q.start) = 2 ∧
      (Q d.radical q.start).relIndex (Z d.radical (p.walk.getVert (p.walk.length-2))) = 2 ∧
      Nat.card (⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ :
        Subgroup (FreeAmalgam d.radical)) = 2 := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hsmall : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex
      (Z d.radical q.start) < 4 := by
    by_contra! hlarge
    obtain ⟨c,t,x,hx,hxc,hat,hct,hgen,r,hr1,hro⟩ :=
      nonsylow_large_backward_step_at_knownSimple (e := e) (hz := hz) (hn := hn)
        hb hns q.path hlarge
    let r' : BackwardShift (h := h) q.path := ⟨c,t,x,hx,hxc,hat,hct,hgen,r,hr1,hro⟩
    obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hns
    have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
      rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
    exact cube_two_backward_shifts_false s hc hb u hR p q r'
  have hi := small_critical_indices s hc q.path hsmall
  exact ⟨hi.1,hi.2,small_critical_commutator_card s hc q.path hsmall⟩

include e hz hn in
/-- The actual large-image branch supplies a generating backward shift
whose two critical images and full commutator all have order two. -/
theorem nonsylow_large_backward_small_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ q : BackwardShift (h := h) p,
      (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical q.start) = 2 ∧
      (Q d.radical q.start).relIndex (Z d.radical (p.walk.getVert (p.walk.length-2))) = 2 ∧
      Nat.card (⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ :
        Subgroup (FreeAmalgam d.radical)) = 2 := by
  obtain ⟨c,t,x,hx,hxc,hat,hct,hgen,v,hv1,hvo⟩ :=
    nonsylow_large_backward_step_at_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p hlarge
  let q : BackwardShift (h := h) p := ⟨c,t,x,hx,hxc,hat,hct,hgen,v,hv1,hvo⟩
  exact ⟨q,nonsylow_generating_backward_shift_indices_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p q⟩

include e hz hn in
/-- Large critical images force a forward slice of index exactly two above
distance four. The bound uses the same prescribed neighbor and actual
backward transporter, with its now-proved small critical image. -/
theorem nonsylow_large_forward_slice_eq_two_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) = 2 := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hel := critical_forward_not_le_slice_of_escape s hc hb2
    (nonsylow_criticalEscape_knownSimple (e := e) (hz := hz) (hn := hn) hb hns) p
  obtain ⟨t,hat,hgen,x,hx,hxt,v,hvt,hover,hsmall⟩ :=
    nonsylow_large_image_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn)
      hb2 hns p hlarge hdelta hel
  have hct : Adjacent d.radical (act d.radical x (p.walk.getVert 2)) t := by
    rw [←hxt]
    exact (adjacent_act_iff d.radical x _ _).mpr hdelta
  let q : BackwardShift (h := h) p := ⟨_,t,x,hx,rfl,hat,hct,hgen,v,hvt,hover⟩
  have hi := (nonsylow_generating_backward_shift_indices_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p q).1
  apply hsmall
  change (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical q.start) < 4
  rw [hi]
  decide

/-- Vertex-transitive transport of the large-image forward slice uses the same
critical walk, second vertex and Baumann subgroup. -/
theorem nonsylow_large_forward_slice_eq_two_at_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) = 2 := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g⁻¹ a) (act d.radical g⁻¹ a'),
      p₀.walk.getVert 2 = act d.radical g⁻¹ (p.walk.getVert 2) :=
    ⟨p.act g⁻¹,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hvert⟩ := hpact
  have hlarge₀ : 4 ≤ (Q d.radical (act d.radical g⁻¹ a')).relIndex
      (Z d.radical (alpha d.radical)) := by
    rw [←hbase,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹⁻¹).injective]
    exact hlarge
  have hB := Escape.PairingControl.FirstPairing.B_act
    (geometry := replacementGeometry h d) (by change 2 < replacementDistance h d; omega)
    g⁻¹ a p.start_color
  rw [hbase,inv_inv] at hB
  have hi := nonsylow_large_forward_slice_eq_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p₀ hlarge₀
  rw [hvert,U_act,inv_inv,hB,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hi
  exact hi

include s in
/-- The whole critical commutator of a generating backward shift is fixed
by the original starting stabilizer, using its actual edge and endpoint
as generators. This accounts for the full stabilizer. -/
theorem cube_backward_commutator_central
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) :
    ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let H := ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆
  have hHt : H ≤ Z d.radical q.edge := by
    simpa only [q.first] using cube_critical_commutator_le_first_seed s hc u hR q.path
  have ht : color d.radical q.edge = true := by
    have hh := adjacent_color_ne d.radical q.adjacent_start
    rw [p.start_color] at hh
    cases he : color d.radical q.edge <;> simp_all
  have hHQ : H ≤ centralizer (Q d.radical q.edge : Set (FreeAmalgam d.radical)) := by
    intro x hx
    have hh := hHt hx
    rw [Z,if_neg (by simp [ht])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  have hHpre : H ≤ Z d.radical (p.walk.getVert (p.walk.length-2)) :=
    ((critical_Z_commutator_le_moving (h := h) q.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)
  have hHend : H ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) := by
    apply (hHpre.trans (Z_le_Q_of_dist_lt d.radical _
      ((replacementGeometry h d).exists_critical _ q.path.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' p.end_color)))
    rw [p.dist_end,(replacementGeometry h d).distance_constant _ q.path.end_color]
    change p.walk.length-(p.walk.length-2) < replacementDistance h d
    have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  apply le_centralizer_iff.mp
  rw [←q.generation]
  exact sup_le (le_centralizer_iff.mp hHQ) (le_centralizer_iff.mp hHend)

include e hz hn in
/-- The literal large-critical-image branch yields an asymmetric pair of
slices on its selected backward path: index two in the original direction
and strictly greater than two in the reverse direction. Its critical line
has order two, is fixed by the whole old stabilizer, and is noncentral at
its own start. No terminal exclusion is assumed. -/
theorem nonsylow_large_backward_asymmetric_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ q : BackwardShift (h := h) p,
      (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical q.start) = 2 ∧
      Nat.card (⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ :
        Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
        centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      (¬ ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
        centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))) ∧
      (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical q.start) = 2 ∧
      2 < (B d.radical q.start ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical a) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨q,hi,_,hcard⟩ := nonsylow_large_backward_small_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p hlarge
  obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  refine ⟨q,hi,hcard,cube_backward_commutator_central s hc hb2 u hR p q,
    critical_commutator_not_central s hc q.path,?_,?_⟩
  · have hB : (B d.radical a ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj q.transporter⁻¹).toMonoidHom =
        B d.radical a ((replacementGeometry h d).Z_normal _) := mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized hb2 a p.start_color
        ((stabilizer d.radical a).inv_mem q.transporter_mem))
    rw [←q.start_eq,U_act,←hB,relIndex_map_map_of_injective
      (f := (MulAut.conj q.transporter⁻¹).toMonoidHom) _ _ (MulAut.conj q.transporter⁻¹).injective]
    exact nonsylow_large_forward_slice_eq_two_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hns p hlarge
  · have hq2 : q.path.walk.getVert 2 = a := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
    have hstrict := nonsylow_small_forward_slice_strict_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hns q.path (by rw [hi]; decide)
    rwa [hq2] at hstrict

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
