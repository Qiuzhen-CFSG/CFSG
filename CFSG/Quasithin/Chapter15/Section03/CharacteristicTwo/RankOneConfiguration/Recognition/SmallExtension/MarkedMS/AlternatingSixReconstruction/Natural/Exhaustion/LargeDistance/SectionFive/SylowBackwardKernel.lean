module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelDecomposition

/-!
# Common-kernel control of non-elementary backward selection

Above distance four, in the order-sixteen radical-image branch, a moving
small critical line D supplements the whole edge-fixed subgroup in the
common full kernel F. Thus every edge subactor has the same displacement
on F and D. A seed at distance at most two from the opposite endpoint
centralizes D. If it lies in the edge core, it therefore centralizes F.

Reversing the actual critical walk applies this to a candidate backward
seed trapped in the predecessor core. Every conjugate of the full
critical kernel contains F with index two. Consequently its centralizer
of the candidate has index at most two. This is a bound on the action of
each full kernel, not an identification of its commutator with that of
the common intersection.

Noncentrality of F on a chosen two-edge seed gives a backward critical
path with that exact first edge and all overlapping vertices retained.
The radius version constructs both the seed and edge. Conversely, a
trapped whole radius centralizes F. The final application uses the actual
restricted original radical and its replacement embedding; Sylow status
is deduced in this branch. Both moving covers and their central
attachments remain present.

Small critical index, line movement and the noncentrality premises of the
selection results remain explicit. The fixed-common-kernel branch,
unconditional backward selection, terminal exclusion, distance-four
estimates and LargeDistanceInput remain with the large-distance owner.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the full-kernel comparisons and backward selection in (5.5)--(5.8),
printed pp.915--920. The argument uses the original natural graph, without
identifying it with the exceptional cubic graph.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowBackwardKernel
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- A seed near the opposite critical endpoint centralizes the common full
kernel whenever it belongs to the first edge core. -/
theorem sixteen_near_seed_common_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hc : color d.radical c = false)
    (hnear : (cosetGraph d.radical).dist c a' ≤ 2)
    (htrap : Z d.radical c ≤ Q d.radical (p.walk.getVert 1)) :
    let F := Z d.radical a ⊓ centralizer
      (componentOrbit (Z d.radical a') (Q d.radical (p.walk.getVert 1)) : Set _)
    F ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) := by
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  have hZQ : Z d.radical c ≤ Q d.radical a' := by
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c hc)
    rw [(replacementGeometry h d).distance_constant c hc]
    change (cosetGraph d.radical).dist c a' < replacementDistance h d
    exact lt_of_le_of_lt hnear (by omega)
  have hDZ : D ≤ Z d.radical a' :=
    (critical_Z_commutator_le_moving (h := h) p).trans
      (inf_le_right.trans (DistanceEight.U_le_Z d.radical a'))
  have hDC : D ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    hDZ.trans ((commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color)).trans (centralizer_le hZQ))
  have hh := SylowKernelDecomposition.sixteen_common_kernel_subactor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hmove (Z d.radical c) htrap
  exact commutator_eq_bot_iff_le_centralizer.mp
    (hh.1.trans (commutator_eq_bot_iff_le_centralizer.mpr hDC))

include e hz hn in
/-- The centralizer of a subgroup centralized by the common kernel has
index at most two in every conjugate full critical kernel. -/
theorem sixteen_common_fixed_full_kernel_indices_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (A : Subgroup (FreeAmalgam d.radical))
    (hFC : Z d.radical a ⊓ centralizer
      (componentOrbit (Z d.radical a') (Q d.radical (p.walk.getVert 1)) : Set _) ≤
        centralizer (A : Set (FreeAmalgam d.radical))) :
    ∀ x ∈ Q d.radical (p.walk.getVert 1),
      (centralizer (A : Set (FreeAmalgam d.radical))).relIndex
        ((Z d.radical a ⊓ Q d.radical a').map (MulAut.conj x).toMonoidHom) ≤ 2 := by
  let T := Q d.radical (p.walk.getVert 1)
  let K := Z d.radical a ⊓ Q d.radical a'
  let F := Z d.radical a ⊓ centralizer
    (componentOrbit (Z d.radical a') T : Set (FreeAmalgam d.radical))
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d)
    hcard p.start_color hat
  have hi := SylowKernelPair.small_seed_orbit_identifications_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p
  have hf := SylowCommonKernel.moving_common_kernel_edge_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall (hT.symm ▸ hmove)
  dsimp only at hi hf
  rw [hT] at hi hf
  have hFZ : F.relIndex (Z d.radical a) = 4 := hf.2.1
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hKZ : K.relIndex (Z d.radical a) = 2 := by
    rw [show K = Z d.radical a ⊓ Q d.radical a' from rfl,inf_relIndex_left]
    exact (small_critical_indices s hcent p hsmall).1
  intro x hx
  let Kx := K.map (MulAut.conj x).toMonoidHom
  have hzx : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a
      (hx.2 a (adjacent_symm d.radical hat)))
  have hxZ : Kx ≤ Z d.radical a := (map_mono inf_le_left).trans_eq hzx
  have hxindex : Kx.relIndex (Z d.radical a) = 2 := by
    change (K.map (MulAut.conj x).toMonoidHom).relIndex (Z d.radical a) = 2
    rw [←hzx,relIndex_map_map_of_injective _ _ (MulAut.conj x).injective]
    exact hKZ
  have hFx : F ≤ Kx := by
    rw [show F = ⨅ t : T, K.map (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom
      from hi.2.2.2]
    exact iInf_le _ (⟨x,hx⟩ : T)
  have hmul := relIndex_mul_relIndex F Kx (Z d.radical a) hFx hxZ
  rw [hFZ,hxindex] at hmul
  have hidx : F.relIndex Kx = 2 := by omega
  let := finite_Z d.radical a
  let : Finite Kx := Finite.of_injective (inclusion hxZ) (inclusion_injective _)
  exact (relIndex_le_of_le_left hFC
    (index_ne_zero_of_finite : F.relIndex Kx ≠ 0)).trans_eq hidx

include e hz hn in
/-- A trapped backward seed centralizes the common reverse kernel. Each
full reverse critical kernel has centralizer index at most two. -/
theorem sixteen_trapped_backward_seed_common_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert (p.walk.length-1)) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hc : color d.radical c = false)
    (hnear : (cosetGraph d.radical).dist c a ≤ 2)
    (htrap : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    let F := Z d.radical a' ⊓ centralizer
      (componentOrbit (Z d.radical a)
        (Q d.radical (p.walk.getVert (p.walk.length-1))) : Set _)
    F ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) ∧
      ∀ x ∈ Q d.radical (p.walk.getVert (p.walk.length-1)),
        (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex
          ((Z d.radical a' ⊓ Q d.radical a).map (MulAut.conj x).toMonoidHom) ≤ 2 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let r : CriticalPath d.radical (replacementGeometry h d) a' a := {
    start_color := p.end_color
    walk := p.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hcent p }
  have hr : r.walk.getVert 1 = p.walk.getVert (p.walk.length-1) :=
    p.walk.getVert_reverse 1
  have hrs : (Q d.radical a).relIndex (Z d.radical a') < 4 := by
    rw [(small_critical_indices s hcent p hsmall).2]
    decide
  have hrm : ¬ Q d.radical (r.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a',Z d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rwa [hr,commutator_comm (Z d.radical a')]
  have hl : 2 < p.walk.length := p.length_eq_b ▸ (by omega : 2 < replacementDistance h d)
  have hct : Adjacent d.radical (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have het : Adjacent d.radical a' (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical (p.walk.getVert (p.walk.length-1)) = true := by
    have hh := adjacent_color_ne d.radical het
    rw [p.end_color] at hh
    cases he : color d.radical (p.walk.getVert (p.walk.length-1)) <;> simp_all
  have htrap' : Z d.radical c ≤ Q d.radical (r.walk.getVert 1) := by
    rw [hr]
    exact htrap.trans (Q_le_adjacent_h d.radical ht hct)
  have hh := sixteen_near_seed_common_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard r hrs hrm hc hnear htrap'
  have hi := sixteen_common_fixed_full_kernel_indices_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard r hrs hrm (Z d.radical c) hh
  dsimp only at hh hi ⊢
  rw [hr] at hh hi
  exact ⟨hh,hi⟩

include e hz hn in
/-- Movement of the common reverse kernel selects a backward critical path
through the prescribed two-edge seed, retaining the entire overlap. -/
theorem sixteen_backward_path_of_common_kernel_movement_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert (p.walk.length-1)) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hnotfixed : ¬ (Z d.radical a' ⊓ centralizer
      (componentOrbit (Z d.radical a)
        (Q d.radical (p.walk.getVert (p.walk.length-1))) : Set _)) ≤
          centralizer (Z d.radical c : Set (FreeAmalgam d.radical))) :
    ∃ q : CriticalPath d.radical (replacementGeometry h d) c
        (p.walk.getVert (p.walk.length-2)),
      q.walk.getVert 1 = t ∧
      (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
      2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical c) := by
  have hc : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [p.start_color] at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  let w : (cosetGraph d.radical).Walk c a :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  have hnear : (cosetGraph d.radical).dist c a ≤ 2 := hw ▸ SimpleGraph.dist_le w
  have hbad : ¬ Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) :=
    fun hh => hnotfixed (sixteen_trapped_backward_seed_common_kernel_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hmove hc hnear hh).1
  let q := p.prepend_two (by exact Nat.le_of_lt (by omega : 2 < replacementDistance h d))
    hc w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  have hover (i : ℕ) (hi : i ≤ p.walk.length-2) :
      q.walk.getVert (i+2) = p.walk.getVert i :=
    p.prepend_two_overlap _ _ _ _ _ hi
  have hqa : q.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := critical_start_slice_index_two_le s hcent (by omega) q
  rw [hqa] at hi
  exact ⟨q,hqt,hover,hi⟩


include e hz hn in
/-- Failure of radius escape forces the whole starting radius to centralize
the common reverse kernel, including its central attachment. -/
theorem sixteen_trapped_radius_common_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert (p.walk.length-1)) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    let F := Z d.radical a' ⊓ centralizer
      (componentOrbit (Z d.radical a)
        (Q d.radical (p.walk.getVert (p.walk.length-1))) : Set _)
    F ≤ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) := by
  apply le_centralizer_iff.mpr
  apply (V_le_iff d.radical p.start_color _).mpr
  intro c hc hca
  have hZV : Z d.radical c ≤ V d.radical a :=
    (V_le_iff d.radical p.start_color _).mp le_rfl c hc hca
  exact le_centralizer_iff.mp
    (sixteen_trapped_backward_seed_common_kernel_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hmove hc hca (hZV.trans htrap)).1

include e hz hn in
/-- Noncentrality on the full radius constructs an actual backward critical
path, its first edge and its nontrivial Baumann slice. -/
theorem sixteen_backward_path_of_radius_kernel_movement_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert (p.walk.length-1)) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hnotfixed : ¬ (Z d.radical a' ⊓ centralizer
      (componentOrbit (Z d.radical a)
        (Q d.radical (p.walk.getVert (p.walk.length-1))) : Set _)) ≤
          centralizer (V d.radical a : Set (FreeAmalgam d.radical))) :
    ∃ c t, Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) := by
  have hescape : ¬ V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) :=
    fun hh => hnotfixed (sixteen_trapped_radius_common_kernel_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hmove hh)
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hd : (cosetGraph d.radical).dist a (p.walk.getVert (p.walk.length-2)) + 2 =
      (replacementGeometry h d).b d.radical := by
    rw [p.dist_start (Nat.sub_le _ _),p.length_eq_b]
    change replacementDistance h d - 2 + 2 = replacementDistance h d
    omega
  obtain ⟨c,hcol,hca,hcrit⟩ := exists_critical_shift d.radical p.start_color hd hescape
  obtain ⟨w,hw⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist c a
  have hwlen : w.length = 2 := hw.trans hca
  let t := w.getVert 1
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      w.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a t := by
    apply adjacent_symm d.radical
    apply (cosetGraph_adj d.radical _ _).mp
    have hh := w.adj_getVert_succ (i := 1) (by omega)
    simpa only [show 1+1=w.length by omega,SimpleGraph.Walk.getVert_length] using hh
  let q := p.prepend_two (Nat.le_of_lt hb2) hcol w hwlen hcrit.2
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hwlen,show 1<2 from by decide,ite_true,t]
  have hover (i : ℕ) (hi : i ≤ p.walk.length-2) :
      q.walk.getVert (i+2) = p.walk.getVert i :=
    p.prepend_two_overlap _ _ _ _ _ hi
  have hqa : q.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  refine ⟨c,t,hat,hct,q,hqt,hover,?_⟩
  have hh := critical_start_slice_index_two_le s hcent hb2 q
  rwa [hqa] at hh

include e hz hn in
/-- The full-kernel centralizer estimates for the literal restricted original
radical and its actual replacement embedding. No original-Sylow premise is added. -/
theorem original_sylow_near_seed_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hmove : ¬ ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) ≤
      centralizer ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _))
    (hc : color d.radical c = false)
    (hnear : (cosetGraph d.radical).dist c a' ≤ 2)
    (htrap : Z d.radical c ≤
      ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let F := Z d.radical (alpha d.radical) ⊓
      centralizer (componentOrbit (Z d.radical a') T : Set (FreeAmalgam d.radical))
    F ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) ∧
      ∀ x ∈ T, (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex
        ((Z d.radical (alpha d.radical) ⊓ Q d.radical a').map
          (MulAut.conj x).toMonoidHom) ≤ 2 := by
  have hrestriction := (SylowLarge.sixteen_original_restriction_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard).2.1
  have hT : ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) =
      Q d.radical (p.walk.getVert 1) := by
    rw [hfirst,Q_beta,hrestriction]
  have hm : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by rwa [hT] at hmove
  have ht : Z d.radical c ≤ Q d.radical (p.walk.getVert 1) := htrap.trans_eq hT
  have hf := sixteen_near_seed_common_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hm hc hnear ht
  have hi := sixteen_common_fixed_full_kernel_indices_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hm (Z d.radical c) hf
  dsimp only at hf hi ⊢
  rw [hT]
  exact ⟨hf,hi⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowBackwardKernel
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

