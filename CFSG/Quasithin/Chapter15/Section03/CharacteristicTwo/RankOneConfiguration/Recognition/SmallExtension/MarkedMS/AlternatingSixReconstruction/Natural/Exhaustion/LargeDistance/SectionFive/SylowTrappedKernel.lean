module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedMover

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardRigidity

/-!
# Movement of the full reverse kernel by a trapped radius

Above distance four, a radius trapped in the predecessor core lies in the
endpoint stabilizer. Its endpoint image is larger than two, whereas the
relative centralizer of any full reverse critical kernel has image order two.
Thus the radius moves every such kernel. Some actual two-edge seed in that
radius must already move the un-conjugated kernel; the moving reverse kernel
has exactly the same nonzero commutator with this seed.

In the order-sixteen radical-image branch, with the prescribed small critical
index and moving critical line, the previously proved common-kernel estimates
show that every full kernel has precisely that common kernel as its radius
fixer. The selected seed has the same fixer, of index two, and its commutator
lies in the intersection of the common kernel with that actual seed. The final
application reverses the original critical path and uses the literal original
radical restriction and replacement embedding. Both covers and their central
attachments are retained.

These estimates handle movement within the trapped-radius branch; they do not
yet exclude that branch. The small-index and moving-line premises, the remaining
backward selection and terminal exclusion, and distance four remain obligations
of the unconditional large-distance assembly.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.7)--(5.8), printed pp.918--920, and the selection in (5.11),
printed pp.923--924. All kernels and vertices belong to the actual natural
characteristic-replacement graph.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedKernel
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem small_kernel_fixer_index
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a) :
    let K := (Z d.radical a ⊓ Q d.radical a').map (MulAut.conj x).toMonoidHom
    (Q d.radical a).relIndex (stabilizer d.radical a ⊓ centralizer (K : Set _)) = 2 := by
  let K := Z d.radical a ⊓ Q d.radical a'
  let J := Q d.radical a ⊔ Z d.radical a'
  have hZa : Z d.radical a' ≤ stabilizer d.radical a :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
      (by rw [(replacementGeometry h d).distance_constant _ p.start_color]
          exact replacementDistance_pos h d) p.critical
  have hJG : J ≤ stabilizer d.radical a := sup_le (fun _ hy => hy.1) hZa
  let := finite_stabilizer d.radical a
  let : Finite J := Finite.of_injective (inclusion hJG) (inclusion_injective _)
  let : ((Q d.radical a).subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (hJG.trans (Q_normalized d.radical a))
  have hi := relIndex_sup_left ((Z d.radical a').subgroupOf J) ((Q d.radical a).subgroupOf J)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at hi
  have hidx : (Q d.radical a).relIndex J = 2 := hi.trans (small_critical_indices s hc p hsmall).2
  have hGmap : (stabilizer d.radical a).map (MulAut.conj x).toMonoidHom =
      stabilizer d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical a).le_normalizer hx)
  have hQmap : (Q d.radical a).map (MulAut.conj x).toMonoidHom = Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp ((Q_normalized d.radical a) hx)
  have he := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom)
    (small_critical_kernel_centralizer_eq s hc p hsmall)
  change (stabilizer d.radical a ⊓ centralizer (K : Set _)).map
    (MulAut.conj x).toMonoidHom = J.map (MulAut.conj x).toMonoidHom at he
  rw [←map_inf_centralizer_of_injective _ (MulAut.conj x).injective,hGmap] at he
  dsimp only
  rw [he,←hQmap,relIndex_map_map_of_injective _ _ (MulAut.conj x).injective]
  exact hidx

include e hz hn in
/-- An actor with endpoint image larger than two moves every conjugate full
critical kernel. Conjugation is within the actual starting stabilizer. -/
theorem small_kernel_conjugates_moved_knownSimple
    (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (A : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ stabilizer d.radical a)
    (hlarge : 2 < (Q d.radical a).relIndex A) :
    ∀ x ∈ stabilizer d.radical a,
      ⁅(Z d.radical a ⊓ Q d.radical a').map (MulAut.conj x).toMonoidHom,A⁆ ≠ ⊥ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  intro x hx hz0
  have hfix := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz0)
  let C := stabilizer d.radical a ⊓ centralizer
    ((Z d.radical a ⊓ Q d.radical a').map (MulAut.conj x).toMonoidHom : Set _)
  have hAC : A ≤ C := le_inf hA hfix
  let := finite_stabilizer d.radical a
  let : Finite C := Finite.of_injective (inclusion (show C ≤ stabilizer d.radical a from inf_le_left))
    (inclusion_injective _)
  have hi := relIndex_le_of_le_right (H := Q d.radical a) hAC index_ne_zero_of_finite
  have hcidx := small_kernel_fixer_index s hc p hsmall x hx
  exact (Nat.not_le_of_gt hlarge) (hi.trans_eq hcidx)

include e hz hn in
/-- Trapping the radius at the predecessor core forces nontrivial action on
all full reverse critical kernels, even before choosing the radical image. -/
theorem trapped_radius_full_kernels_moved_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (htrap : V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    ∀ x ∈ stabilizer d.radical a',
      ⁅(Z d.radical a' ⊓ Q d.radical a).map (MulAut.conj x).toMonoidHom,
        V d.radical a⁆ ≠ ⊥ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let r : CriticalPath d.radical (replacementGeometry h d) a' a := {
    start_color := p.end_color
    walk := p.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc p }
  have hrs : (Q d.radical a).relIndex (Z d.radical a') < 4 := by
    rw [(small_critical_indices s hc p hsmall).2]
    decide
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
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
  have hVG : V d.radical a ≤ stabilizer d.radical a' :=
    (htrap.trans (Q_le_adjacent_h d.radical ht hct)).trans
      (fun _ hx => hx.2 a' (adjacent_symm d.radical het))
  have hi := (critical_radius_indices_gt_seed s hc hb2 p).1
  rw [(small_critical_indices s hc p hsmall).1] at hi
  exact small_kernel_conjugates_moved_knownSimple (e := e) (hz := hz) (hn := hn)
    hb2 r hrs (V d.radical a) hVG hi

include e hz hn in
/-- Every full reverse kernel has precisely the common kernel as its
radius centralizer. Its action is nontrivial and has fixed index two. -/
theorem sixteen_trapped_radius_kernel_centralizers_knownSimple
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
    ∀ x ∈ T,
      ⁅K.map (MulAut.conj x).toMonoidHom,V d.radical a⁆ ≠ ⊥ ∧
      (centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (K.map (MulAut.conj x).toMonoidHom) = 2 ∧
      K.map (MulAut.conj x).toMonoidHom ⊓
        centralizer (V d.radical a : Set (FreeAmalgam d.radical)) = F ∧
      ⁅K.map (MulAut.conj x).toMonoidHom,V d.radical a⁆ ≤ F ⊓ V d.radical a := by
  let T := Q d.radical (p.walk.getVert (p.walk.length-1))
  let K := Z d.radical a' ⊓ Q d.radical a
  let F := Z d.radical a' ⊓ centralizer (componentOrbit (Z d.radical a) T : Set _)
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
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
  have hk := SylowTrappedMover.sixteen_small_mover_full_kernel_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard r hrs hrm
  have ht := SylowTrappedMover.sixteen_trapped_radius_full_kernels_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hmove htrap
  have hFC := SylowBackwardKernel.sixteen_trapped_radius_common_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hmove htrap
  dsimp only at hk ht hFC ⊢
  rw [hr] at hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have het : Adjacent d.radical a' (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,
      p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  intro x hx
  let Kx := K.map (MulAut.conj x).toMonoidHom
  let C := Kx ⊓ centralizer (V d.radical a : Set (FreeAmalgam d.radical))
  have hxG : x ∈ stabilizer d.radical a' := hx.2 a' (adjacent_symm d.radical het)
  have hne : ⁅Kx,V d.radical a⁆ ≠ ⊥ :=
    trapped_radius_full_kernels_moved_knownSimple (e := e) (hz := hz) (hn := hn)
      hb p hsmall htrap x hxG
  have hFx : F ≤ Kx := (hk x hx).1
  have hFidx : F.relIndex Kx = 2 := (hk x hx).2.1
  have hZmap : (Z d.radical a').map (MulAut.conj x).toMonoidHom = Z d.radical a' :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a' hxG)
  have hxZ : Kx ≤ Z d.radical a' := (map_mono inf_le_left).trans_eq hZmap
  let := finite_Z d.radical a'
  let : Finite Kx := Finite.of_injective (inclusion hxZ) (inclusion_injective _)
  have hidx : (centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex Kx = 2 := by
    have hle : (centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex Kx ≤ 2 :=
      (ht.2.2.2 x hx).2.2
    have hpos : 0 < (centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex Kx :=
      Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hone : (centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex Kx ≠ 1 :=
      fun hh => hne (commutator_eq_bot_iff_le_centralizer.mpr (relIndex_eq_one.mp hh))
    omega
  have hFCx : F ≤ C := le_inf hFx hFC
  have hCidx : C.relIndex Kx = 2 := by
    change (Kx ⊓ centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex Kx = 2
    rwa [inf_relIndex_left]
  have hmul := relIndex_mul_relIndex F C Kx hFCx inf_le_left
  rw [hFidx,hCidx] at hmul
  have hCF : C ≤ F := relIndex_eq_one.mp (by omega : F.relIndex C = 1)
  exact ⟨hne,hidx,le_antisymm hCF hFCx,(ht.2.2.2 x hx).2.1⟩

include e hz hn in
/-- A trapped radius supplies a genuine two-edge backward seed moved by the
full reverse critical kernel. No radical-image restriction is needed. -/
theorem trapped_radius_moving_seed_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (htrap : V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    ∃ c t, color d.radical c = false ∧
      (cosetGraph d.radical).dist c a = 2 ∧
      Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
      Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) ∧
      ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ ≠ ⊥ ∧
      ⁅U d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ =
        ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ ∧
      ⁅U d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ ≠ ⊥ := by
  let K := Z d.radical a' ⊓ Q d.radical a
  have h1 : (MulAut.conj (1 : FreeAmalgam d.radical)).toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro z
    simp
  have hne : ⁅K,V d.radical a⁆ ≠ ⊥ := by
    simpa only [h1,Subgroup.map_id] using
      trapped_radius_full_kernels_moved_knownSimple (e := e) (hz := hz) (hn := hn)
        hb p hsmall htrap 1 (stabilizer d.radical a').one_mem
  have hex : ∃ c, color d.radical c = false ∧
      (cosetGraph d.radical).dist c a ≤ 2 ∧ ⁅K,Z d.radical c⁆ ≠ ⊥ := by
    by_contra! hh
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    apply (V_le_iff d.radical p.start_color _).mpr
    intro c hc hca
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hh c hc hca))
  obtain ⟨c,hc,hca,hm⟩ := hex
  have htwo : (cosetGraph d.radical).dist c a = 2 := by
    have hzero : (cosetGraph d.radical).dist c a ≠ 0 := by
      intro hh
      have he := (cosetGraph_connected d.radical).dist_eq_zero_iff.mp hh
      subst c
      apply hm
      rw [commutator_comm]
      exact le_bot_iff.mp ((commutator_mono le_rfl inf_le_right).trans_eq
        (Z_centralizes_Q d.radical a p.start_color))
    have heven : Even ((cosetGraph d.radical).dist c a) := by
      obtain ⟨w,hw⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist c a
      rw [←hw,walk_even_iff_color_eq,hc,p.start_color]
    rw [Nat.even_iff] at heven
    omega
  obtain ⟨t,hct,hat⟩ := exists_common_neighbor_of_dist_two d.radical c a htwo
  have hZV : Z d.radical c ≤ V d.radical a :=
    (V_le_iff d.radical p.start_color _).mp le_rfl c hc hca
  have hZtrap := hZV.trans htrap
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega : 2 < replacementDistance h d)
  have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have heq := (critical_kernel_predecessor_moving s hcent (by omega) p).2.2
    (Z d.radical c) hZtrap
  exact ⟨c,t,hc,htwo,hat,hct,hZtrap,hm,heq.symm,heq ▸ hm⟩

include e hz hn in
/-- The selected two-edge seed has nontrivial action and exactly the common
kernel as its fixer in the full reverse critical kernel. -/
theorem sixteen_trapped_radius_selected_seed_knownSimple
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
    ∃ c t, color d.radical c = false ∧
      (cosetGraph d.radical).dist c a = 2 ∧
      Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
      Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) ∧
      ⁅K,Z d.radical c⁆ ≠ ⊥ ∧
      ⁅U d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ = ⁅K,Z d.radical c⁆ ∧
      ⁅U d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ ≠ ⊥ ∧
      (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex K = 2 ∧
      K ⊓ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) = F ∧
      ⁅K,Z d.radical c⁆ ≤ F ⊓ Z d.radical c := by
  let T := Q d.radical (p.walk.getVert (p.walk.length-1))
  let K := Z d.radical a' ⊓ Q d.radical a
  let F := Z d.radical a' ⊓ centralizer (componentOrbit (Z d.radical a) T : Set _)
  obtain ⟨c,t,hc,hca,hat,hct,hZtrap,hne,hmeq,hmne⟩ := trapped_radius_moving_seed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall htrap
  have hZV : Z d.radical c ≤ V d.radical a :=
    (V_le_iff d.radical p.start_color _).mp le_rfl c hc hca.le
  have hfix := sixteen_trapped_radius_kernel_centralizers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hmove htrap 1 T.one_mem
  have h1 : (MulAut.conj (1 : FreeAmalgam d.radical)).toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro z
    simp
  simp only [h1,Subgroup.map_id] at hfix
  have hfixeq : K ⊓ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) = F :=
    hfix.2.2.1
  have hidxK : F.relIndex K = 2 := by
    rw [←hfixeq,inf_relIndex_left]
    exact hfix.2.1
  have hFC : F ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    SylowBackwardKernel.sixteen_trapped_backward_seed_common_kernel_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hmove hc hca.le hZtrap |>.1
  let := finite_Z d.radical a'
  let : Finite K := Finite.of_injective (inclusion (show K ≤ Z d.radical a' from inf_le_left))
    (inclusion_injective _)
  let C := K ⊓ centralizer (Z d.radical c : Set (FreeAmalgam d.radical))
  have hFCx : F ≤ C := le_inf (hfixeq.symm.le.trans inf_le_left) hFC
  have hidx : (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex K = 2 := by
    have hle := (relIndex_le_of_le_left hFC
      (index_ne_zero_of_finite : F.relIndex K ≠ 0)).trans_eq hidxK
    have hpos : 0 < (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex K :=
      Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hone : (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex K ≠ 1 :=
      fun hh => hne (commutator_eq_bot_iff_le_centralizer.mpr (relIndex_eq_one.mp hh))
    omega
  have hCidx : C.relIndex K = 2 := by
    change (K ⊓ centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex K = 2
    rwa [inf_relIndex_left]
  have hmul := relIndex_mul_relIndex F C K hFCx inf_le_left
  rw [hidxK,hCidx] at hmul
  have hCF : C = F := le_antisymm (relIndex_eq_one.mp (by omega : F.relIndex C = 1)) hFCx
  have hKG : K ≤ stabilizer d.radical c :=
    (show K ≤ Q d.radical a from inf_le_right).trans
      (fun _ hx => (Q_le_adjacent_h d.radical (by
        have hh := adjacent_color_ne d.radical hat
        rw [p.start_color] at hh
        cases he : color d.radical t <;> simp_all) hat hx).2 c (adjacent_symm d.radical hct))
  have hcomm : ⁅K,Z d.radical c⁆ ≤ F ⊓ Z d.radical c := le_inf
    ((commutator_mono le_rfl hZV).trans hfix.2.2.2 |>.trans inf_le_left)
    (le_normalizer_iff_commutator_le_right.mp (hKG.trans (Z_normalized d.radical c)))
  exact ⟨c,t,hc,hca,hat,hct,hZtrap,hne,hmeq,hmne,hidx,hCF,hcomm⟩

include e hz hn in
/-- The selected seed for the literal original MS radical, restricted to
its replacement overgroup and embedded by the original amalgam map. -/
theorem original_sylow_trapped_radius_selected_seed_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hmove : ¬ ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) ≤
      centralizer ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : V d.radical a' ≤ Q d.radical (p.walk.getVert 2)) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let K := Z d.radical (alpha d.radical) ⊓ Q d.radical a'
    let F := Z d.radical (alpha d.radical) ⊓
      centralizer (componentOrbit (Z d.radical a') T : Set (FreeAmalgam d.radical))
    ∃ c t, color d.radical c = false ∧
      (cosetGraph d.radical).dist c a' = 2 ∧
      Adjacent d.radical a' t ∧ Adjacent d.radical c t ∧
      Z d.radical c ≤ Q d.radical (p.walk.getVert 2) ∧
      ⁅K,Z d.radical c⁆ ≠ ⊥ ∧
      ⁅U d.radical (alpha d.radical) ⊓ Q d.radical a',Z d.radical c⁆ = ⁅K,Z d.radical c⁆ ∧
      ⁅U d.radical (alpha d.radical) ⊓ Q d.radical a',Z d.radical c⁆ ≠ ⊥ ∧
      (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex K = 2 ∧
      K ⊓ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) = F ∧
      ⁅K,Z d.radical c⁆ ≤ F ⊓ Z d.radical c := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let r : CriticalPath d.radical (replacementGeometry h d) a' (alpha d.radical) := {
    start_color := p.end_color
    walk := p.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc p }
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hr1 : r.walk.getVert (r.walk.length-1) = p.walk.getVert 1 := by
    change p.walk.reverse.getVert (p.walk.reverse.length-1) = p.walk.getVert 1
    rw [SimpleGraph.Walk.length_reverse,p.walk.getVert_reverse]
    congr 1
    omega
  have hr2 : r.walk.getVert (r.walk.length-2) = p.walk.getVert 2 := by
    change p.walk.reverse.getVert (p.walk.reverse.length-2) = p.walk.getVert 2
    rw [SimpleGraph.Walk.length_reverse,p.walk.getVert_reverse]
    congr 1
    omega
  have hrs : (Q d.radical (alpha d.radical)).relIndex (Z d.radical a') < 4 := by
    rw [(small_critical_indices s hc p hsmall).2]
    decide
  have hrestriction := (SylowLarge.sixteen_original_restriction_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 hcard).2.1
  have hT : ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) =
      Q d.radical (p.walk.getVert 1) := by
    rw [hfirst,Q_beta,hrestriction]
  have hrm : ¬ Q d.radical (r.walk.getVert (r.walk.length-1)) ≤ centralizer
      ((⁅Z d.radical a',Z d.radical (alpha d.radical)⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rwa [hr1,commutator_comm (Z d.radical a'),←hT]
  have hh := sixteen_trapped_radius_selected_seed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard r hrs hrm (hr2.symm ▸ htrap)
  dsimp only at hh ⊢
  rw [hr1,hr2,←hT] at hh
  exact hh

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedKernel
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

