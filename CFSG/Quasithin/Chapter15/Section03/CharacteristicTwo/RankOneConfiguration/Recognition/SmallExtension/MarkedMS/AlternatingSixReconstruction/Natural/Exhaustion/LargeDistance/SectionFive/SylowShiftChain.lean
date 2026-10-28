module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowForwardSpan

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowLargeCritical
/-!
# Generating shifts and common kernels for the image-sixteen replacement

The controlled large-image actor and the proved small-image strict slice
supply a generating backward shift for every critical path. The same local
transporter sends both the old first edge and second vertex to the chosen
ones; conjugation preserves this data at every original component vertex.

Two successive generating shifts cannot end in a large critical image:
SylowLargeCritical would make the noncentral first-edge intersection central
at its own critical start. The second shifted pair therefore has both
critical indices two and a commutator of order two. Its noncentrality at the
intermediate vertex forces the whole first-edge kernel to move that line.
This discharges the movement premise in the existing full common-kernel
calculation, giving index four, the order-at-most-two kernel commutator and
the literal small-mover centralizers and conjugate-kernel estimates.

Three successive choices give the source R4/R6 lines on the original walk,
with both first-edge movements and the same endpoint radius centralizing
both lines. The original-radical application uses its proved restriction
inside the replacement overgroup and the same amalgam transporter. Both
moving covers and every central attachment are retained. The source (5.10)
mover equality and containment, terminal exclusion and distance-four
argument remain separate obligations.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.7)--(5.11), printed pp.919--924; in particular the first
critical-image reduction and R4/R6 configuration on p.922.
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

namespace SylowShiftChain
private theorem sixteen_backward_step_base
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    ∃ c t x, x ∈ stabilizer d.radical (alpha d.radical) ∧
      act d.radical x (p.walk.getVert 1) = t ∧
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
  by_cases hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))
  · have hel := critical_forward_not_le_slice_of_escape s hc hb2
      (sixteen_criticalEscape_knownSimple
        (e := e) (hz := hz) (hn := hn) hb hcard) p
    obtain ⟨t,hat,hgen,x,hx,hxt,q,hqt,hover⟩ :=
      SylowLarge.sixteen_large_image_backward_shift_knownSimple
        (e := e) (hz := hz) (hn := hn) hb2 hcard p hlarge hdelta hel
    refine ⟨_,t,x,hx,hxt,rfl,hat,?_,hgen,q,hqt,hover⟩
    rw [←hxt]
    exact (adjacent_act_iff d.radical x _ _).mpr hdelta
  · obtain ⟨t,hat,x,hx,hxt,hct,hgen,_,q,hqt,hover⟩ :=
      SylowForwardSpan.sixteen_small_backward_shift_of_four_lt_knownSimple
        (e := e) (hz := hz) (hn := hn) hb hcard p (by omega)
    exact ⟨_,t,x,hx,hxt,rfl,hat,hct,hgen,q,hqt,hover⟩

/-- Above distance four both critical-image branches supply a backward shift.
The chosen local conjugator and every shared vertex are retained. -/
theorem sixteen_backward_step_at_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ c t x, x ∈ stabilizer d.radical a ∧
      act d.radical x (p.walk.getVert 1) = t ∧
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
  have base := sixteen_backward_step_base hb hcard
    (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  obtain ⟨c,t,x,hx,hxt,hxc,hat,hct,hgen,q,hq1,hover⟩ := base (p.act g⁻¹)
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
  refine ⟨act d.radical g c,act d.radical g t,y,?_,?_,?_,?_,?_,?_,r,hr1,hrover⟩
  · change act d.radical y a = a
    rw [hy,show act d.radical x (act d.radical g⁻¹ a) = act d.radical g⁻¹ a from hx,hcancel]
  · rw [hy]
    have hh := congrArg (act d.radical g) hxt
    simpa only [CriticalPath.act,actWalk_getVert] using hh
  · rw [hy,hxc]
  · simpa only [hcancel] using (adjacent_act_iff d.radical g _ _).mpr hat
  · exact (adjacent_act_iff d.radical g _ _).mpr hct
  · have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hcancel,hcancel] at he
    exact he

/-- Every image-sixteen critical path admits an actual generating backward shift. -/
theorem backwardShift_with_edge
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') : ∃ q : BackwardShift (h := h) p,
      act d.radical q.transporter (p.walk.getVert 1) = q.edge := by
  obtain ⟨c,t,x,hx,hxt,hxc,hat,hct,hgen,q,hq1,hqo⟩ :=
    sixteen_backward_step_at_knownSimple hb hcard p
  exact ⟨⟨c,t,x,hx,hxc,hat,hct,hgen,q,hq1,hqo⟩,hxt⟩

include e hz hn in
/-- Two generating backward shifts have small critical image and a
noncentral line at the intermediate vertex. -/
theorem two_backward_shifts_small_moving_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    (¬ ⁅Z d.radical r.start,Z d.radical z⁆ ≤
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))) ∧
    (Q d.radical z).relIndex (Z d.radical r.start) = 2 ∧
    (Q d.radical r.start).relIndex (Z d.radical z) = 2 ∧
    Nat.card (⁅Z d.radical r.start,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
    ¬ Q d.radical (r.path.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical r.start,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
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
  have hsmall : (Q d.radical (q.path.walk.getVert (q.path.walk.length-2))).relIndex
      (Z d.radical r.start) < 4 := by
    by_contra! hlarge
    exact SylowLargeCritical.large_critical_three_shift_generators_false s hc r.path hlarge
      q.start q.edge a (p.walk.getVert (p.walk.length-2)) a'
      (by rw [r.first]; exact r.adjacent_start) q.adjacent_shift
      (by rw [r.first]; exact r.generation) q.generation
      (hcent _ q.path.end_color (by omega)) (hcent _ p.end_color (by omega))
      r.transporter r.transporter_mem hyz
  have hi := small_critical_indices s hc r.path hsmall
  refine ⟨hnc,hi.1,hi.2,small_critical_commutator_card s hc r.path hsmall,?_⟩
  intro hfixed
  apply hnc
  apply le_centralizer_iff.mp
  rw [←r.generation]
  exact sup_le (by simpa only [r.first] using hfixed)
    (le_centralizer_iff.mp (hcent _ q.path.end_color (by omega)))

/-- The actual second shifted line supplies the previously explicit movement
premise for the full common-kernel calculation. -/
theorem two_backward_shifts_common_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let T := Q d.radical (r.path.walk.getVert 1)
    let D := ⁅Z d.radical r.start,Z d.radical z⁆
    let K := Z d.radical r.start ⊓ Q d.radical z
    let F := Z d.radical r.start ⊓ centralizer (componentOrbit (Z d.radical z) T : Set _)
    let J := SmallMover.join (U d.radical r.start) (Q d.radical r.start) T 4
    F.relIndex (Z d.radical r.start) = 4 ∧
      Nat.card (⁅F,T⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
      ⁅F,T⁆ ≤ Z d.radical (r.path.walk.getVert 1) ∧
      ⁅F,T⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical)) ∧
      T ⊓ centralizer (D : Set (FreeAmalgam d.radical)) = J ∧
      T ⊓ centralizer (F : Set (FreeAmalgam d.radical)) = J ∧
      T ⊓ normalizer (K : Set (FreeAmalgam d.radical)) = J ∧
      ∀ x ∈ T,
        F ≤ K.map (MulAut.conj x).toMonoidHom ∧
        F.relIndex (K.map (MulAut.conj x).toMonoidHom) = 2 ∧
        ⁅K.map (MulAut.conj x).toMonoidHom,J⁆ ≤ F ∧
        ⁅⁅K.map (MulAut.conj x).toMonoidHom,J⁆,J⁆ = ⊥ := by
  have hd := two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r
  have hsmall : (Q d.radical (q.path.walk.getVert (q.path.walk.length-2))).relIndex
      (Z d.radical r.start) < 4 := by rw [hd.2.1]; decide
  have hm := hd.2.2.2.2
  have hat : Adjacent d.radical r.start (r.path.walk.getVert 1) := by
    rw [r.first]
    exact r.adjacent_shift
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d)
    hcard r.path.start_color hat
  have hf := SylowCommonKernel.moving_common_kernel_edge_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r.path hsmall (hT.symm ▸ hm)
  dsimp only at hf ⊢
  rw [hT] at hf
  have hfix := SylowTrappedMover.sixteen_common_kernel_centralizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard r.path hsmall hm
  have hact := SylowTrappedMover.sixteen_small_mover_full_kernel_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard r.path hsmall hm
  exact ⟨hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2,
    hfix.1,hfix.2.1,hfix.2.2.1,hact⟩

/-- The image-sixteen replacement constructs two successive shifts. The
second has an index-two critical image, a noncentral line moved by its first
edge, and a strict forward slice; no small-image premise remains. -/
theorem sixteen_two_backward_shifts_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path),
      act d.radical q.transporter (p.walk.getVert 1) = q.edge ∧
      act d.radical r.transporter (q.path.walk.getVert 1) = r.edge ∧
      q.path.walk.getVert (q.path.walk.length-2) = p.walk.getVert (p.walk.length-4) ∧
      let z := q.path.walk.getVert (q.path.walk.length-2)
      (Q d.radical z).relIndex (Z d.radical r.start) = 2 ∧
      (Q d.radical r.start).relIndex (Z d.radical z) = 2 ∧
      Nat.card (⁅Z d.radical r.start,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      (¬ ⁅Z d.radical r.start,Z d.radical z⁆ ≤
        centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))) ∧
      (¬ Q d.radical (r.path.walk.getVert 1) ≤ centralizer
        ((⁅Z d.radical r.start,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
      2 < (B d.radical r.start ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical q.start) ∧
      let T := Q d.radical (r.path.walk.getVert 1)
      let D := ⁅Z d.radical r.start,Z d.radical z⁆
      let F := Z d.radical r.start ⊓ centralizer (componentOrbit (Z d.radical z) T : Set _)
      let J := SmallMover.join (U d.radical r.start) (Q d.radical r.start) T 4
      F.relIndex (Z d.radical r.start) = 4 ∧
        Nat.card (⁅F,T⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
        T ⊓ centralizer (D : Set (FreeAmalgam d.radical)) = J ∧
        T ⊓ centralizer (F : Set (FreeAmalgam d.radical)) = J := by
  obtain ⟨q,hqedge⟩ := backwardShift_with_edge hb hcard p
  obtain ⟨r,hredge⟩ := backwardShift_with_edge hb hcard q.path
  have hd := two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r
  have hsmall : (Q d.radical (q.path.walk.getVert (q.path.walk.length-2))).relIndex
      (Z d.radical r.start) < 4 := by rw [hd.2.1]; decide
  have hstrict := SylowForwardSpan.sixteen_small_forward_slice_strict_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard r.path hsmall
  have hr2 : r.path.walk.getVert 2 = q.start := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using r.overlap 0 (Nat.zero_le _)
  rw [hr2] at hstrict
  have hp : p.walk.length = replacementDistance h d := p.length_eq_b
  have hq : q.path.walk.length = replacementDistance h d := q.path.length_eq_b
  have he4 : q.path.walk.getVert (q.path.walk.length-2) = p.walk.getVert (p.walk.length-4) := by
    rw [show q.path.walk.length-2 = (p.walk.length-4)+2 by omega]
    exact q.overlap _ (by omega)
  have hker := two_backward_shifts_common_kernel_knownSimple hb hcard p q r
  exact ⟨q,r,hqedge,hredge,he4,hd.2.1,hd.2.2.1,hd.2.2.2.1,hd.1,hd.2.2.2.2,hstrict,
    hker.1,hker.2.1,hker.2.2.2.2.1,hker.2.2.2.2.2.1⟩


/-- Three successive generating shifts realize the source R4/R6 configuration.
Both critical images are two, both lines are moved by their first edge kernels,
and the same endpoint radius centralizes both lines. -/
theorem sixteen_three_backward_shifts_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
      (t : BackwardShift (h := h) r.path),
      act d.radical q.transporter (p.walk.getVert 1) = q.edge ∧
      act d.radical r.transporter (q.path.walk.getVert 1) = r.edge ∧
      act d.radical t.transporter (r.path.walk.getVert 1) = t.edge ∧
      q.path.walk.getVert (q.path.walk.length-2) = p.walk.getVert (p.walk.length-4) ∧
      r.path.walk.getVert (r.path.walk.length-2) = p.walk.getVert (p.walk.length-6) ∧
      let z₄ := p.walk.getVert (p.walk.length-4)
      let z₆ := p.walk.getVert (p.walk.length-6)
      let H₄ := ⁅Z d.radical r.start,Z d.radical z₄⁆
      let H₆ := ⁅Z d.radical t.start,Z d.radical z₆⁆
      (Q d.radical z₄).relIndex (Z d.radical r.start) = 2 ∧
      (Q d.radical z₆).relIndex (Z d.radical t.start) = 2 ∧
      Nat.card H₄ = 2 ∧ Nat.card H₆ = 2 ∧
      (¬ H₄ ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))) ∧
      (¬ H₆ ≤ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical))) ∧
      (¬ Q d.radical r.edge ≤ centralizer (H₄ : Set (FreeAmalgam d.radical))) ∧
      (¬ Q d.radical t.edge ≤ centralizer (H₆ : Set (FreeAmalgam d.radical))) ∧
      H₄ ⊔ H₆ ≤ centralizer (V d.radical z₄ : Set (FreeAmalgam d.radical)) := by
  obtain ⟨q,hqe⟩ := backwardShift_with_edge hb hcard p
  obtain ⟨r,hre⟩ := backwardShift_with_edge hb hcard q.path
  obtain ⟨t,hte⟩ := backwardShift_with_edge hb hcard r.path
  have hfour := two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r
  have hsix := two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q.path r t
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
    rw [show r.path.walk.length-2 = (q.path.walk.length-4)+2 by omega,r.overlap _ (by omega)]
    rw [show q.path.walk.length-4 = (p.walk.length-6)+2 by omega]
    exact q.overlap _ (by omega)
  have hVQ : V d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤
      Q d.radical (q.path.walk.getVert (q.path.walk.length-2)) :=
    V_le_Q d.radical (geometry := replacementGeometry h d) r.path.end_color (by change 2 < replacementDistance h d; omega)
  have hVQ₆ : V d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤
      Q d.radical (r.path.walk.getVert (r.path.walk.length-2)) := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) r.path.end_color
    rw [SimpleGraph.dist_comm,r.path.dist_end]
    change r.path.walk.length-(r.path.walk.length-2)+2 < replacementDistance h d
    omega
  have hcentral : ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ⊔
      ⁅Z d.radical t.start,Z d.radical (r.path.walk.getVert (r.path.walk.length-2))⁆ ≤
      centralizer (V d.radical (q.path.walk.getVert (q.path.walk.length-2)) : Set (FreeAmalgam d.radical)) := by
    apply sup_le
    · exact (((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right).trans
        (DistanceEight.U_le_Z d.radical _)).trans
        ((commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical _ r.path.end_color)).trans (centralizer_le hVQ))
    · exact (((critical_Z_commutator_le_moving (h := h) t.path).trans inf_le_right).trans
        (DistanceEight.U_le_Z d.radical _)).trans
        ((commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical _ t.path.end_color)).trans (centralizer_le hVQ₆))
  dsimp only at hfour hsix ⊢
  rw [r.first,he4] at hfour
  rw [t.first,he6] at hsix
  simp only [he4,he6] at hcentral
  exact ⟨q,r,t,hqe,hre,hte,he4,he6,hfour.2.1,hsix.2.1,
    hfour.2.2.2.1,hsix.2.2.2.1,hfour.1,hsix.1,hfour.2.2.2.2,hsix.2.2.2.2,hcentral⟩

/-- Literal transport of the restricted original MS radical to the chosen
generating edge, with no critical-image-size assumption. -/
theorem original_radical_backward_shift_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    ∃ q : BackwardShift (h := h) p,
      act d.radical q.transporter (beta d.radical) = q.edge ∧
      T.map (MulAut.conj q.transporter⁻¹).toMonoidHom = Q d.radical q.edge ∧
      T.map (MulAut.conj q.transporter⁻¹).toMonoidHom ⊔ Z d.radical a' =
        stabilizer d.radical (alpha d.radical) := by
  obtain ⟨q,hq⟩ := backwardShift_with_edge hb hcard p
  rw [hfirst] at hq
  obtain ⟨_,hR,_⟩ := SylowLarge.sixteen_original_restriction_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard
  have hT : (((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)).map
      (MulAut.conj q.transporter⁻¹).toMonoidHom = Q d.radical q.edge := by
    rw [←hR,←Q_beta,←Q_act,hq]
  exact ⟨q,hq,hT,hT.symm ▸ q.generation⟩

end SylowShiftChain
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
