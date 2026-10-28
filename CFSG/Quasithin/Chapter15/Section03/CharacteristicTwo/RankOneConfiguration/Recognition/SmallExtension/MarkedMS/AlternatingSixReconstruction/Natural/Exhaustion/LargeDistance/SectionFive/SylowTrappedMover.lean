module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowBackwardKernel
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# Full-kernel normalization in the trapped Sylow-radius branch

Above distance four, assume the canonical radical image has order sixteen
and the first edge moves a small critical line D. Its maximum small mover J
is exactly the edge centralizer of D, exactly the edge centralizer of the
common full kernel F, and exactly the relative normalizer of the original
full critical kernel K. Since J is normal in the edge core, it normalizes
every conjugate Kx. The quotient Kx/F has order two, so [Kx,J] lies in F
and is centralized by J.

The opposite two-core intersected with the edge core centralizes D.
It therefore lies in J, normalizes every Kx and acts quadratically on the
whole starting seed. This conclusion uses the two full kernels generating
that seed; a centralizer-index bound alone would not give normalization.

Reversing the actual critical path applies this to a whole radius trapped
in the predecessor core. Its commutator with the full endpoint seed lies
in F intersected with that actual radius. Each full reverse kernel is
normalized and has radius-centralizer index at most two. The last theorem
uses the literal restriction of the original MS radical and its replacement
embedding. Both moving covers and all central attachments are retained;
Sylow status is obtained only in this order-sixteen image branch.

These estimates address the fixed-common-kernel branch of backward
selection. They do not yet exclude a trapped radius. Small critical index,
line movement, the remaining non-elementary selection and terminal
contradiction, and the distance-four exclusion still require discharge
in the large-distance assembly.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.5)--(5.8), printed pp.915--920, especially the full-kernel
normalization step in (5.7). The graph and maps remain the natural
replacement graph, without an identification with the exceptional graph.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedMover
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- The maximum small mover is the edge centralizer of both the critical
line and common kernel, and normalizes every full critical-kernel conjugate. -/
theorem sixteen_common_kernel_centralizer_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let D := ⁅Z d.radical a,Z d.radical a'⁆
    let K := Z d.radical a ⊓ Q d.radical a'
    let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
    let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
    T ⊓ centralizer (D : Set (FreeAmalgam d.radical)) = J ∧
      T ⊓ centralizer (F : Set (FreeAmalgam d.radical)) = J ∧
      T ⊓ normalizer (K : Set (FreeAmalgam d.radical)) = J ∧
      ∀ x ∈ T,
        J ≤ normalizer (K.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) := by
  let T := Q d.radical (p.walk.getVert 1)
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  let K := Z d.radical a ⊓ Q d.radical a'
  let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
  let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d)
    hcard p.start_color hat
  have hk := SylowSmallMovers.small_critical_kernel_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  dsimp only at hk
  rw [hT] at hk
  have hJ := SylowAdjacent.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p.start_color hat
  have hJnorm : T ≤ normalizer (J : Set (FreeAmalgam d.radical)) := hJ.2.2.2.2.1
  have hJT : J ≤ T := hJ.2.1
  have hTK : T ⊓ normalizer (K : Set (FreeAmalgam d.radical)) = J := hk.2.2.2 hmove
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hKN := small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall
  have hTG : T ≤ stabilizer d.radical a := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hTC : T ⊓ centralizer (D : Set (FreeAmalgam d.radical)) = J := by
    apply le_antisymm
    · intro x hx
      have hn : x ∈ stabilizer d.radical a ⊓ normalizer (K : Set (FreeAmalgam d.radical)) := by
        rw [hKN]
        exact ⟨hTG hx.1,hx.2⟩
      rw [←hTK]
      exact ⟨hx.1,hn.2⟩
    · exact le_inf hJT hk.2.1
  have hJF : J ≤ centralizer (F : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    have hh := SylowKernelDecomposition.sixteen_common_kernel_subactor_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hmove J hJT
    exact hh.1.trans (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hk.2.1))
  have hDF : D ≤ F := (le_componentOrbit D T).trans
    (SylowKernelDecomposition.sixteen_common_kernel_line_displacement_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hmove).1
  have hTF : T ⊓ centralizer (F : Set (FreeAmalgam d.radical)) = J :=
    le_antisymm ((inf_le_inf_left _ (centralizer_le hDF)).trans_eq hTC) (le_inf hJT hJF)
  refine ⟨hTC,hTF,hTK,?_⟩
  intro x hx
  have hJx : J.map (MulAut.conj x).toMonoidHom = J :=
    mem_normalizer_iff_map_conj_eq.mp (hJnorm hx)
  calc
    J = J.map (MulAut.conj x).toMonoidHom := hJx.symm
    _ ≤ (normalizer (K : Set (FreeAmalgam d.radical))).map
        (MulAut.conj x).toMonoidHom := map_mono hk.2.2.1
    _ ≤ normalizer (K.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) :=
      K.le_normalizer_map _

include e hz hn in
/-- Every full critical kernel has an index-two common kernel; the maximum
small mover acts trivially modulo that kernel and fixes it pointwise. -/
theorem sixteen_small_mover_full_kernel_commutator_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let K := Z d.radical a ⊓ Q d.radical a'
    let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
    let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
    ∀ x ∈ T,
      F ≤ K.map (MulAut.conj x).toMonoidHom ∧
      F.relIndex (K.map (MulAut.conj x).toMonoidHom) = 2 ∧
      ⁅K.map (MulAut.conj x).toMonoidHom,J⁆ ≤ F ∧
      ⁅⁅K.map (MulAut.conj x).toMonoidHom,J⁆,J⁆ = ⊥ := by
  let T := Q d.radical (p.walk.getVert 1)
  let K := Z d.radical a ⊓ Q d.radical a'
  let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
  let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
  have hfix := sixteen_common_kernel_centralizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hmove
  have hJF : J ≤ centralizer (F : Set (FreeAmalgam d.radical)) := by
    have hh : J ≤ T ⊓ centralizer (F : Set (FreeAmalgam d.radical)) := hfix.2.1.symm.le
    exact hh.trans inf_le_right
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
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hKZ : K.relIndex (Z d.radical a) = 2 := by
    rw [show K = Z d.radical a ⊓ Q d.radical a' from rfl,inf_relIndex_left]
    exact (small_critical_indices s hc p hsmall).1
  dsimp only
  intro x hx
  let Kx := K.map (MulAut.conj x).toMonoidHom
  have hZmap : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp
      (Z_normalized d.radical a (hx.2 a (adjacent_symm d.radical hat)))
  have hxZ : Kx ≤ Z d.radical a := (map_mono inf_le_left).trans_eq hZmap
  have hxidx : Kx.relIndex (Z d.radical a) = 2 := by
    change (K.map (MulAut.conj x).toMonoidHom).relIndex (Z d.radical a) = 2
    rw [←hZmap,relIndex_map_map_of_injective _ _ (MulAut.conj x).injective]
    exact hKZ
  have hFx : F ≤ Kx := by
    rw [show F = ⨅ t : T, K.map (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom
      from hi.2.2.2]
    exact iInf_le _ (⟨x,hx⟩ : T)
  have hmul := relIndex_mul_relIndex F Kx (Z d.radical a) hFx hxZ
  have hFZ : F.relIndex (Z d.radical a) = 4 := hf.2.1
  rw [hFZ,hxidx] at hmul
  have hidx : F.relIndex Kx = 2 := by omega
  have hcomm : ⁅Kx,J⁆ ≤ F := commutator_le_of_normalized_index_two Kx F J
    hFx hidx (hfix.2.2.2 x hx) (hJF.trans (Subgroup.centralizer_le_normalizer _))
  refine ⟨hFx,hidx,hcomm,?_⟩
  exact le_bot_iff.mp ((commutator_mono hcomm le_rfl).trans_eq
    (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hJF)))


include e hz hn in
/-- The actual opposite-core intersection lies in the maximum small mover.
It normalizes each full critical kernel and acts quadratically on the whole seed. -/
theorem sixteen_opposite_core_full_kernel_control_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let A := T ⊓ Q d.radical a'
    let K := Z d.radical a ⊓ Q d.radical a'
    let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
    let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
    A ≤ J ∧ A ≤ centralizer (F : Set (FreeAmalgam d.radical)) ∧
      ⁅Z d.radical a,A⁆ ≤ F ∧ ⁅⁅Z d.radical a,A⁆,A⁆ = ⊥ ∧
      ∀ x ∈ T,
        A ≤ normalizer (K.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) ∧
        ⁅K.map (MulAut.conj x).toMonoidHom,A⁆ ≤ F ∧
        (centralizer (A : Set (FreeAmalgam d.radical))).relIndex
          (K.map (MulAut.conj x).toMonoidHom) ≤ 2 := by
  classical
  let T := Q d.radical (p.walk.getVert 1)
  let A := T ⊓ Q d.radical a'
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  let K := Z d.radical a ⊓ Q d.radical a'
  let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
  let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
  have hf := sixteen_common_kernel_centralizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hmove
  have hk := sixteen_small_mover_full_kernel_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hmove
  have hD : D ≤ Z d.radical a' := (critical_Z_commutator_le_moving (h := h) p).trans
    (inf_le_right.trans (DistanceEight.U_le_Z d.radical a'))
  have hAD : A ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color))).trans (centralizer_le hD))
  have hAJ : A ≤ J := (le_inf inf_le_left hAD).trans_eq hf.1
  have hJF : J ≤ centralizer (F : Set (FreeAmalgam d.radical)) :=
    hf.2.1.symm.le.trans inf_le_right
  have hAF : A ≤ centralizer (F : Set (FreeAmalgam d.radical)) := hAJ.trans hJF
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d)
    hcard p.start_color hat
  obtain ⟨x,hx,hxm⟩ := SetLike.not_le_iff_exists.mp hmove
  have hp := SylowKernelPair.small_kernel_pair_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall x (hT.symm ▸ hx) hxm
  have hgen : K ⊔ K.map (MulAut.conj x).toMonoidHom = Z d.radical a := hp.2.2.1
  have hZmap : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp
      (Z_normalized d.radical a (hx.2 a (adjacent_symm d.radical hat)))
  have hxZ : K.map (MulAut.conj x).toMonoidHom ≤ Z d.radical a :=
    (map_mono inf_le_left).trans_eq hZmap
  have h1 : (MulAut.conj (1 : FreeAmalgam d.radical)).toMonoidHom =
      MonoidHom.id (FreeAmalgam d.radical) := by
    apply MonoidHom.ext
    intro y
    simp
  have hKJ : ⁅K,J⁆ ≤ F := by
    simpa only [h1,Subgroup.map_id] using (hk 1 T.one_mem).2.2.1
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  have hZF : Z d.radical a ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
    ((le_centralizer (Z d.radical a)).trans (centralizer_le inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hZJ : ⁅Z d.radical a,J⁆ ≤ F := by
    rw [←hgen]
    exact commutator_sup_le_of_relative_normal (Z d.radical a) K
      (K.map (MulAut.conj x).toMonoidHom) J F hZF inf_le_left hxZ hKJ (hk x hx).2.2.1
  have hZA : ⁅Z d.radical a,A⁆ ≤ F := (commutator_mono le_rfl hAJ).trans hZJ
  refine ⟨hAJ,hAF,hZA,?_,?_⟩
  · exact le_bot_iff.mp ((commutator_mono hZA le_rfl).trans_eq
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hAF)))
  · intro y hy
    exact ⟨hAJ.trans (hf.2.2.2 y hy),(commutator_mono le_rfl hAJ).trans (hk y hy).2.2.1,
      SylowBackwardKernel.sixteen_common_fixed_full_kernel_indices_knownSimple
        (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hmove A
        (le_centralizer_iff.mp hAF) y hy⟩

include e hz hn in
/-- A trapped radius lies in the reverse maximum small mover, normalizes
every full reverse kernel and moves the endpoint seed into the common kernel
intersected with the actual radius. -/
theorem sixteen_trapped_radius_full_kernels_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert (p.walk.length-1)) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    let T := Q d.radical (p.walk.getVert (p.walk.length-1))
    let K := Z d.radical a' ⊓ Q d.radical a
    let F := Z d.radical a' ⊓ centralizer (componentOrbit (Z d.radical a) T : Set _)
    let J := SmallMover.join (U d.radical a') (Q d.radical a') T 4
    V d.radical a ≤ J ∧
      ⁅Z d.radical a',V d.radical a⁆ ≤ F ⊓ V d.radical a ∧
      ⁅⁅Z d.radical a',V d.radical a⁆,V d.radical a⁆ = ⊥ ∧
      ∀ x ∈ T,
        V d.radical a ≤ normalizer
          (K.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) ∧
        ⁅K.map (MulAut.conj x).toMonoidHom,V d.radical a⁆ ≤ F ⊓ V d.radical a ∧
        (centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex
          (K.map (MulAut.conj x).toMonoidHom) ≤ 2 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let r : CriticalPath d.radical (replacementGeometry h d) a' a := {
    start_color := p.end_color
    walk := p.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc p }
  have hr : r.walk.getVert 1 = p.walk.getVert (p.walk.length-1) :=
    p.walk.getVert_reverse 1
  have hrs : (Q d.radical a).relIndex (Z d.radical a') < 4 := by
    rw [(small_critical_indices s hc p hsmall).2]
    decide
  have hrm : ¬ Q d.radical (r.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a',Z d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rwa [hr,commutator_comm (Z d.radical a')]
  have hh := sixteen_opposite_core_full_kernel_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard r hrs hrm
  dsimp only at hh ⊢
  rw [hr] at hh
  let T := Q d.radical (p.walk.getVert (p.walk.length-1))
  let K := Z d.radical a' ⊓ Q d.radical a
  let F := Z d.radical a' ⊓ centralizer (componentOrbit (Z d.radical a) T : Set _)
  let A := T ⊓ Q d.radical a
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
  have hVA : V d.radical a ≤ A := le_inf
    (htrap.trans (Q_le_adjacent_h d.radical ht hct))
    (V_le_Q d.radical (geometry := replacementGeometry h d) p.start_color (by exact (show 2 < replacementDistance h d by omega)))
  have hVF : V d.radical a ≤ centralizer (F : Set (FreeAmalgam d.radical)) :=
    hVA.trans hh.2.1
  have hZV : Z d.radical a' ≤ normalizer (V d.radical a : Set (FreeAmalgam d.radical)) :=
    (critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
      (by rw [(replacementGeometry h d).distance_constant a p.start_color]
          exact replacementDistance_pos h d) p.critical).trans (DistanceEight.V_normalized d.radical a)
  have hcomm : ⁅Z d.radical a',V d.radical a⁆ ≤ F :=
    (commutator_mono le_rfl hVA).trans hh.2.2.1
  refine ⟨hVA.trans hh.1,le_inf hcomm
    (le_normalizer_iff_commutator_le_right.mp hZV),?_,?_⟩
  · exact le_bot_iff.mp ((commutator_mono hcomm le_rfl).trans_eq
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hVF)))
  · intro x hx
    have hZmap : (Z d.radical a').map (MulAut.conj x).toMonoidHom = Z d.radical a' :=
      mem_normalizer_iff_map_conj_eq.mp
        (Z_normalized d.radical a' (hx.2 a' (adjacent_symm d.radical het)))
    have hxZ : K.map (MulAut.conj x).toMonoidHom ≤ Z d.radical a' :=
      (map_mono inf_le_left).trans_eq hZmap
    have hnorm := hh.2.2.2.2 x hx
    refine ⟨hVA.trans hnorm.1,le_inf
      ((commutator_mono le_rfl hVA).trans hnorm.2.1)
      (le_normalizer_iff_commutator_le_right.mp (hxZ.trans hZV)),?_⟩
    exact SylowBackwardKernel.sixteen_common_fixed_full_kernel_indices_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard r hrs hrm (V d.radical a)
      (by simpa only [hr] using le_centralizer_iff.mp hVF) x (by simpa only [hr] using hx)

include e hz hn in
/-- The opposite-core control on the literal restriction of the original MS
radical, with its original embedding into the replacement amalgam. -/
theorem original_sylow_opposite_core_full_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hmove : ¬ ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) ≤
      centralizer ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let A := T ⊓ Q d.radical a'
    let K := Z d.radical (alpha d.radical) ⊓ Q d.radical a'
    let F := Z d.radical (alpha d.radical) ⊓
      centralizer (componentOrbit (Z d.radical a') T : Set (FreeAmalgam d.radical))
    let J := SmallMover.join (U d.radical (alpha d.radical))
      (Q d.radical (alpha d.radical)) T 4
    A ≤ J ∧ A ≤ centralizer (F : Set (FreeAmalgam d.radical)) ∧
      ⁅Z d.radical (alpha d.radical),A⁆ ≤ F ∧
      ⁅⁅Z d.radical (alpha d.radical),A⁆,A⁆ = ⊥ ∧
      ∀ x ∈ T,
        A ≤ normalizer (K.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) ∧
        ⁅K.map (MulAut.conj x).toMonoidHom,A⁆ ≤ F ∧
        (centralizer (A : Set (FreeAmalgam d.radical))).relIndex
          (K.map (MulAut.conj x).toMonoidHom) ≤ 2 := by
  have hrestriction := (SylowLarge.sixteen_original_restriction_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard).2.1
  have hT : ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) =
      Q d.radical (p.walk.getVert 1) := by
    rw [hfirst,Q_beta,hrestriction]
  have hm : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by rwa [hT] at hmove
  have hh := sixteen_opposite_core_full_kernel_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hm
  dsimp only at hh ⊢
  rw [hT]
  exact hh
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedMover
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
