module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.StrictSlices

/-!
# Three backward shifts on the original full-point replacement

For critical distance greater than four, the small-image strict-slice theorem
and the large-image backward argument together construct a backward shift
for every critical path. Conjugation transports this result to every component
vertex, preserving the actual transporter, generating edge and every shared
vertex. Three successive choices give one coherent path configuration; its
last two endpoints are explicitly the original vertices four and six steps
before the endpoint.

The literal commutators R4 and R6 are noncentral at their intermediate
vertices. If either were central there, its containment in an incident edge
kernel would put it in that edge's omega-center seed. Neighbor transitivity,
the next generating edge and the same component conjugator would then make it
central at its own critical endpoint, contradicting the faithful natural
quotient. A small critical image would itself force the forbidden intermediate
centrality. Hence both critical images have order at least four and both
opposite-radius indices exceed eight.

The actual radius at the original vertex a'-4 centralizes R4 and R6. Its
strict index supplies the two alternatives in the last paragraph of (5.11):
its image at a-2 has order greater than two, or its intersection with Q_(a-2)
has image at a-4 of order greater than two. The remaining implication from
these alternatives to a central R4 or R6 is not asserted here. The other
radical images and the distance-four contradiction also remain necessary
for the unconditional distance bound.

All statements use the original characteristic replacement, both moved-cover
orders sixteen and thirty-two, and the canonical quotient action. The
intermediate noncentrality is proved on these paths; it is not inferred merely
from noncentrality at their critical endpoints.

Source: Meierfrankenfeld--Stellmacher (1993), (5.7)--(5.11), pp.919--924,
especially the configuration and terminal index alternative on p.924. The
two-generator transport adapts SymplecticSetup.LargeDistance to both central
covers, using the checked critical-line and quotient-action results here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem full_point_backward_step_base
    (hb : 4 < replacementDistance h d) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
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
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  by_cases hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))
  · obtain ⟨t,hat,hgen⟩ := full_point_generating_neighbor s hc u hf p
    have hel := critical_forward_not_le_slice_of_escape s hc hb2
      (full_point_criticalEscape s hc hb2 u hf) p
    obtain ⟨x,hx,hxt,q,hqt,hover,_⟩ :=
      large_image_backward_shift s hc hb2 u hf.le p hlarge hdelta hel hat hgen
    refine ⟨_,t,x,hx,rfl,hat,?_,hgen,q,hqt,hover⟩
    rw [←hxt]
    exact (adjacent_act_iff d.radical x _ _).mpr hdelta
  · obtain ⟨t,hat,hgen,x,hx,hxt,q,hqt,hover,_⟩ :=
      full_point_small_backward_shift_of_four_lt_knownSimple hb u hfull p (by omega)
    refine ⟨_,t,x,hx,rfl,hat,?_,hgen,q,hqt,hover⟩
    rw [←hxt]
    exact (adjacent_act_iff d.radical x _ _).mpr hdelta

/-- Above distance four both critical-image branches supply a backward shift.
The chosen local conjugator and every shared vertex are retained. -/
theorem full_point_backward_step_at_knownSimple
    (hb : 4 < replacementDistance h d) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
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
  have base := full_point_backward_step_base hb u hfull
    (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  obtain ⟨c,t,x,hx,hxc,hat,hct,hgen,q,hq1,hover⟩ := base (p.act g⁻¹)
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

private theorem central_fixed_map {F : Type*} [Group F] (H K : Subgroup F)
    (hHK : H ≤ centralizer (K : Set F)) {x : F} (hx : x ∈ K) :
    H.map (MulAut.conj x).toMonoidHom = H :=
  mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.mp hHK hx))

/-- In the actual three-position configuration the critical commutator is
noncentral at the middle vertex. The proof transports an edge seed through
the same middle stabilizer and uses the second generating edge; endpoint
noncentrality alone is not substituted for this assertion. -/
theorem critical_commutator_not_central_at_shift_vertex
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (c v z k : Vertex d.radical)
    (hct : Adjacent d.radical c (p.walk.getVert 1)) (hcv : Adjacent d.radical c v)
    (hgen : Q d.radical v ⊔ Z d.radical k = stabilizer d.radical z)
    (hHk : ⁅Z d.radical a,Z d.radical a'⁆ ≤ centralizer (Z d.radical k : Set (FreeAmalgam d.radical)))
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical c)
    (hxa : act d.radical x z = a) :
    ¬ ⁅Z d.radical a,Z d.radical a'⁆ ≤
      centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
  let H := ⁅Z d.radical a,Z d.radical a'⁆
  intro hHC
  have hpos : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) hpos
  have ht : color d.radical (p.walk.getVert 1) = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases he : color d.radical (p.walk.getVert 1) <;> simp_all
  have hHZ : H ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical a)
  have hZaQ : Z d.radical a ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant a p.start_color]
    exact replacementDistance_pos h d
  have hHQt := (hHZ.trans hZaQ).trans (Q_le_adjacent_h d.radical ht hat)
  have hQtC : Q d.radical (p.walk.getVert 1) ≤ stabilizer d.radical c :=
    fun _ he => he.2 _ (adjacent_symm d.radical hct)
  have hHseed : H ≤ Z d.radical (p.walk.getVert 1) := by
    intro z hz
    rw [Z,if_neg (by simp [ht])]
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
    exact mem_omegaCenter_iff.mpr ⟨hHQt hz,
      elemPow_eq_one_of_isElementaryAbelian z (hHZ hz),
      (hHC.trans (centralizer_le hQtC)) hz⟩
  have hHv : H ≤ Z d.radical v := by
    obtain ⟨y,hy,hyt⟩ := stabilizer_transitive_neighbors d.radical c hct hcv
    rw [←hyt,Z_act,←central_fixed_map H (stabilizer d.radical c) hHC
      ((stabilizer d.radical c).inv_mem hy)]
    exact map_mono hHseed
  have hc0 : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  have hv : color d.radical v = true := by
    have hh := adjacent_color_ne d.radical hcv
    rw [hc0] at hh
    cases he : color d.radical v <;> simp_all
  have hHvQ : H ≤ centralizer (Q d.radical v : Set (FreeAmalgam d.radical)) := by
    intro z hz
    have hh := hHv hz
    rw [Z,if_neg (by simp [hv])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  have hHZ : H ≤ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    rw [←hgen]
    exact sup_le (le_centralizer_iff.mp hHvQ) (le_centralizer_iff.mp hHk)
  apply critical_commutator_not_central s hc p
  change H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
  rw [←hxa,stabilizer_act]
  have hh := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hHZ).trans
    (map_centralizer_le_centralizer_image _ _)
  rwa [central_fixed_map H (stabilizer d.radical c) hHC
    ((stabilizer d.radical c).inv_mem hx)] at hh

/-- Two successive local generators force a small critical line to be
central at its own start. This contradicts its original quotient action;
the possible central line of the moved cover is retained. -/
theorem small_critical_three_shift_generators_false
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (c v z f k : Vertex d.radical)
    (hct : Adjacent d.radical c (p.walk.getVert 1)) (hcv : Adjacent d.radical c v)
    (hgenC : Q d.radical (p.walk.getVert 1) ⊔ Z d.radical f = stabilizer d.radical c)
    (hgenZ : Q d.radical v ⊔ Z d.radical k = stabilizer d.radical z)
    (hHf : ⁅Z d.radical a,Z d.radical a'⁆ ≤ centralizer (Z d.radical f : Set (FreeAmalgam d.radical)))
    (hHk : ⁅Z d.radical a,Z d.radical a'⁆ ≤ centralizer (Z d.radical k : Set (FreeAmalgam d.radical)))
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical c)
    (hxa : act d.radical x z = a) : False := by
  let H := ⁅Z d.radical a,Z d.radical a'⁆
  have hHseed : H ≤ Z d.radical (p.walk.getVert 1) :=
    small_critical_line_le_first_seed_of_abelian_image s hc hab p hsmall
  have ht : color d.radical (p.walk.getVert 1) = true := by
    have hpos : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
    have hh := p.vertex_color (show 1 ≤ p.walk.length by omega)
    have hf : ¬ color d.radical (p.walk.getVert 1) = false := by
      intro he
      have hn := hh.mp he
      norm_num at hn
    cases he : color d.radical (p.walk.getVert 1) <;> simp_all
  have hseed (w : Vertex d.radical) (hw : color d.radical w = true) :
      Z d.radical w ≤ centralizer (Q d.radical w : Set (FreeAmalgam d.radical)) := by
    intro r hr
    rw [Z,if_neg (by simp [hw])] at hr
    exact (mem_omegaCenter_iff.mp hr).2.2
  have hHC : H ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    rw [←hgenC]
    exact sup_le (le_centralizer_iff.mp (hHseed.trans (hseed _ ht)))
      (le_centralizer_iff.mp hHf)
  have hHv : H ≤ Z d.radical v := by
    obtain ⟨y,hy,hyt⟩ := stabilizer_transitive_neighbors d.radical c hct hcv
    rw [←hyt,Z_act]
    rw [←central_fixed_map H (stabilizer d.radical c) hHC
      ((stabilizer d.radical c).inv_mem hy)]
    exact map_mono hHseed
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  have hv : color d.radical v = true := by
    have hh := adjacent_color_ne d.radical hcv
    rw [hcol] at hh
    cases he : color d.radical v <;> simp_all
  have hHZ : H ≤ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    rw [←hgenZ]
    exact sup_le (le_centralizer_iff.mp (hHv.trans (hseed _ hv)))
      (le_centralizer_iff.mp hHk)
  have hHA : H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    rw [←hxa,stabilizer_act]
    have hh := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hHZ).trans
      (map_centralizer_le_centralizer_image _ _)
    rwa [central_fixed_map H (stabilizer d.radical c) hHC
      ((stabilizer d.radical c).inv_mem hx)] at hh
  exact critical_commutator_not_central s hc p hHA


/-- A literal backward critical shift. The new start is a local conjugate
of the old second vertex, and the overlap retains every old vertex up to
its predecessor. -/
structure BackwardShift {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') where
  start : Vertex d.radical
  edge : Vertex d.radical
  transporter : FreeAmalgam d.radical
  transporter_mem : transporter ∈ stabilizer d.radical a
  start_eq : act d.radical transporter (p.walk.getVert 2) = start
  adjacent_start : Adjacent d.radical a edge
  adjacent_shift : Adjacent d.radical start edge
  generation : Q d.radical edge ⊔ Z d.radical a' = stabilizer d.radical a
  path : CriticalPath d.radical (replacementGeometry h d) start
    (p.walk.getVert (p.walk.length-2))
  first : path.walk.getVert 1 = edge
  overlap : ∀ i ≤ p.walk.length-2, path.walk.getVert (i+2) = p.walk.getVert i

private theorem backwardShift_nonempty
    (hb : 4 < replacementDistance h d) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') : Nonempty (BackwardShift (h := h) p) := by
  obtain ⟨c,t,x,hx,hxc,hat,hct,hgen,q,hq1,hqo⟩ :=
    full_point_backward_step_at_knownSimple hb u hfull p
  exact ⟨⟨c,t,x,hx,hxc,hat,hct,hgen,q,hq1,hqo⟩⟩

/-- Two actual backward shifts force large critical image and strict radius
indices at the second shifted pair, and noncentrality at its intermediate
vertex. The assertions concern the same paths and transporters. -/
theorem two_backward_shifts_bounds_knownSimple
    (hb : 4 < replacementDistance h d) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    (¬ ⁅Z d.radical r.start,Z d.radical z⁆ ≤
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))) ∧
    4 ≤ (Q d.radical z).relIndex (Z d.radical r.start) ∧
    8 < (Q d.radical z).relIndex (V d.radical r.start) ∧
    8 < (Q d.radical r.start).relIndex (V d.radical z) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥ := by
    let := pointCore_elementary
    let : IsElementaryAbelian 2 (pointCore.map (MulAut.conj u).toMonoidHom) :=
      IsElementaryAbelian.map _
    rw [hf]
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff_isMulCommutative.mpr inferInstance)
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
  have hHe : ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) :=
    ((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)
  have hcent (w : Vertex d.radical) (hw : color d.radical w = false)
      (hdist : (cosetGraph d.radical).dist (q.path.walk.getVert (q.path.walk.length-2)) w < replacementDistance h d) :
      ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
        centralizer (Z d.radical w : Set (FreeAmalgam d.radical)) := by
    apply (hHe.trans (Z_le_Q_of_dist_lt d.radical _
      ((replacementGeometry h d).exists_critical _ r.path.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical w hw)))
    rwa [(replacementGeometry h d).distance_constant _ r.path.end_color]
  have hnc := critical_commutator_not_central_at_shift_vertex s hc r.path
    q.start q.edge a a' (by rw [r.first]; exact r.adjacent_start)
    q.adjacent_shift q.generation (hcent _ p.end_color (by omega)) r.transporter r.transporter_mem hyz
  have hlarge : 4 ≤ (Q d.radical (q.path.walk.getVert (q.path.walk.length-2))).relIndex
      (Z d.radical r.start) := by
    by_contra! hsmall
    exact small_critical_three_shift_generators_false s hc hab r.path hsmall
      q.start q.edge a (p.walk.getVert (p.walk.length-2)) a'
      (by rw [r.first]; exact r.adjacent_start) q.adjacent_shift
      (by rw [r.first]; exact r.generation) q.generation
      (hcent _ q.path.end_color (by omega)) (hcent _ p.end_color (by omega))
      r.transporter r.transporter_mem hyz
  exact ⟨hnc,hlarge,critical_radius_index_gt_eight s hc hb2 r.path hlarge,
    opposite_radius_index_gt_eight s hc hb2 r.path hlarge⟩

private theorem index_gt_four_alternative {F : Type*} [Group F]
    (A C W : Subgroup F) [Finite W] (hindex : 4 < A.relIndex W) :
    2 < C.relIndex W ∨ 2 < A.relIndex (W ⊓ C) := by
  have hi : A.relIndex W ≤ (A ⊓ C).relIndex W :=
    relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
  rw [←relIndex_inf_mul_relIndex] at hi
  by_contra! hsmall
  have hA : A.relIndex (C ⊓ W) ≤ 2 := by
    rw [inf_comm C W]
    exact hsmall.2
  have hh := Nat.mul_le_mul hA hsmall.1
  omega

private theorem backward_shifts_radius_alternative
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hindex : 8 < (Q d.radical r.start).relIndex
      (V d.radical (q.path.walk.getVert (q.path.walk.length-2)))) :
    let z₄ := q.path.walk.getVert (q.path.walk.length-2)
    let z₆ := r.path.walk.getVert (r.path.walk.length-2)
    (2 < (Q d.radical q.start).relIndex (V d.radical z₄) ∨
      2 < (Q d.radical r.start).relIndex (V d.radical z₄ ⊓ Q d.radical q.start)) ∧
    (⁅Z d.radical r.start,Z d.radical z₄⁆ ⊔ ⁅Z d.radical t.start,Z d.radical z₆⁆ ≤
      centralizer (V d.radical z₄ : Set (FreeAmalgam d.radical))) := by
  let z₄ := q.path.walk.getVert (q.path.walk.length-2)
  let z₆ := r.path.walk.getVert (r.path.walk.length-2)
  have hb2 : 2 < replacementDistance h d := by omega
  have hVQ : V d.radical z₄ ≤ Q d.radical z₄ :=
    V_le_Q d.radical (geometry := replacementGeometry h d) r.path.end_color hb2
  have hVQ₆ : V d.radical z₄ ≤ Q d.radical z₆ := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) r.path.end_color
    change (cosetGraph d.radical).dist
      (q.path.walk.getVert (q.path.walk.length-2))
      (r.path.walk.getVert (r.path.walk.length-2)) + 2 < replacementDistance h d
    rw [SimpleGraph.dist_comm,r.path.dist_end]
    have hl : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
    omega
  constructor
  · let V₄ := V d.radical z₄
    let A := Q d.radical r.start
    let C := Q d.radical q.start
    let := finite_stabilizer d.radical z₄
    let : Finite V₄ := Finite.of_injective
      (inclusion (hVQ.trans (fun _ he => he.1))) (inclusion_injective _)
    exact index_gt_four_alternative A C V₄ ((by decide : 4 < 8).trans hindex)
  · apply sup_le
    · exact (((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right).trans
        (DistanceEight.U_le_Z d.radical z₄)).trans
        ((commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical z₄ r.path.end_color)).trans (centralizer_le hVQ))
    · exact (((critical_Z_commutator_le_moving (h := h) t.path).trans inf_le_right).trans
        (DistanceEight.U_le_Z d.radical z₆)).trans
        ((commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical z₆ t.path.end_color)).trans (centralizer_le hVQ₆))

/-- The full-point replacement supplies a coherent three-shift chain.
Its literal R4 and R6 commutators are noncentral at the corresponding
intermediate vertices, and both endpoint radius indices are greater than
eight for both pairs. No natural-subgroup or zero-center hypothesis is used. -/
theorem full_point_three_backward_shifts_knownSimple
    (hb : 4 < replacementDistance h d) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path) (t : BackwardShift (h := h) r.path),
      q.path.walk.getVert (q.path.walk.length-2) = p.walk.getVert (p.walk.length-4) ∧
      r.path.walk.getVert (r.path.walk.length-2) = p.walk.getVert (p.walk.length-6) ∧
      let z₄ := p.walk.getVert (p.walk.length-4)
      let z₆ := p.walk.getVert (p.walk.length-6)
      (¬ ⁅Z d.radical r.start,Z d.radical z₄⁆ ≤
        centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))) ∧
      (¬ ⁅Z d.radical t.start,Z d.radical z₆⁆ ≤
        centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical))) ∧
      4 ≤ (Q d.radical z₄).relIndex (Z d.radical r.start) ∧
      4 ≤ (Q d.radical z₆).relIndex (Z d.radical t.start) ∧
      8 < (Q d.radical z₄).relIndex (V d.radical r.start) ∧
      8 < (Q d.radical r.start).relIndex (V d.radical z₄) ∧
      8 < (Q d.radical z₆).relIndex (V d.radical t.start) ∧
      8 < (Q d.radical t.start).relIndex (V d.radical z₆) ∧
      (2 < (Q d.radical q.start).relIndex (V d.radical z₄) ∨
        2 < (Q d.radical r.start).relIndex (V d.radical z₄ ⊓ Q d.radical q.start)) ∧
      (⁅Z d.radical r.start,Z d.radical z₄⁆ ⊔ ⁅Z d.radical t.start,Z d.radical z₆⁆ ≤
        centralizer (V d.radical z₄ : Set (FreeAmalgam d.radical))) := by
  obtain ⟨q⟩ := backwardShift_nonempty hb u hfull p
  obtain ⟨r⟩ := backwardShift_nonempty hb u hfull q.path
  obtain ⟨t⟩ := backwardShift_nonempty hb u hfull r.path
  have hfour := two_backward_shifts_bounds_knownSimple hb u hfull p q r
  have hsix := two_backward_shifts_bounds_knownSimple hb u hfull q.path r t
  have hterminal := backward_shifts_radius_alternative hb p q r t hfour.2.2.2
  have hp : p.walk.length = replacementDistance h d := p.length_eq_b
  have hq : q.path.walk.length = replacementDistance h d := q.path.length_eq_b
  have hr : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
  have h6 : 6 ≤ replacementDistance h d := by
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he
    omega
  have he4 : q.path.walk.getVert (q.path.walk.length-2) = p.walk.getVert (p.walk.length-4) := by
    rw [show q.path.walk.length-2 = (p.walk.length-4)+2 by omega]
    exact q.overlap _ (by omega)
  have he6 : r.path.walk.getVert (r.path.walk.length-2) = p.walk.getVert (p.walk.length-6) := by
    rw [show r.path.walk.length-2 = ((p.walk.length-6)+2)+2 by omega,
      r.overlap _ (by omega),q.overlap _ (by omega)]
  dsimp only at hfour hsix hterminal
  rw [he4] at hfour
  rw [he6] at hsix
  refine ⟨q,r,t,he4,he6,hfour.1,hsix.1,hfour.2.1,hsix.2.1,
    hfour.2.2.1,hfour.2.2.2,hsix.2.2.1,hsix.2.2.2,?_⟩
  simpa only [he4,he6] using hterminal

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
