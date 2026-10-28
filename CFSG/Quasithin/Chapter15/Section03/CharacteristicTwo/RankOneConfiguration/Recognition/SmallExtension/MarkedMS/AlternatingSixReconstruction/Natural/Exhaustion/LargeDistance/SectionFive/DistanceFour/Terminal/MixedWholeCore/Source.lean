module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.KernelDerived
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SourceKernelFailure
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelObstruction

/-!
# The paired full-kernel obstruction in the strict mixed branch

Keep the backward selector and the single conjugator supplying both paired
edge generation and paired endpoint generation. The two endpoint seeds
cannot both normalize the same full backward-kernel join: the existing
small-section argument would put that join in the Baumann subgroup, contrary
to the strict slice. This uses the whole kernel, including central attachments.

If normalization fails for the original endpoint, its order-two failure line
is exactly the commutator of the full endpoint kernel with the whole midpoint
core. The known failure-line centrality at the starting vertex and the retained
holomorph agreement show that this line cannot be fixed at the midpoint.
`strict_source_obstruction_knownSimple` applies these two calculations to the
literal alpha-based mixed strict branch, retaining the same two generation
identities and kernel containment.

This is a reduction of that branch, not the mixed terminal exclusion. The
second endpoint's normalization failure remains on the original backward
kernel. No equality with the conjugated kernel is asserted. The new common-kernel derived transfer bypasses the endpoint estimate in
the terminal application. The derived and cross-commutator estimates for the
entire residual core `[Q_v,Ltilde_v]` still require proof; the movement line
here is not that residual core or its derived subgroup.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.12)(1),(3), printed pp.924--927. The private import reuses the
proved normalized-actor contradiction without changing its public boundary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- Paired endpoint generation excludes simultaneous normalization of the
same full backward-kernel join. -/
theorem paired_normalization_false_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : MixedBackwardShift (h := h) p)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (x : FreeAmalgam d.radical)
    (hgen : Q d.radical q.edge ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
      stabilizer d.radical a)
    (hnorm : Z d.radical z ≤ normalizer
      (((Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hnormx : Z d.radical (act d.radical x z) ≤ normalizer
      (((Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hq2 : q.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let W := Z d.radical z ⊔ Z d.radical (act d.radical x z)
  have hWG : W ≤ stabilizer d.radical a := by
    rw [←hgen]
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hcentral := (mixed_selected_span_derived_data_knownSimple hb u him p q)
  have hfix : ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (W : Set (FreeAmalgam d.radical)) := by
    rw [hl]
    exact (hcentral.1.symm.le.trans hcentral.2.2).trans (centralizer_le hWG)
  apply strict_small_normalized_actor_false s hc hb q.path
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q.path) W
  · simpa only [q.first,hq2,W,←sup_assoc] using hgen
  · simpa only [hq2,q.index_eq] using hstrict
  · simpa only [hl,hq2] using sup_le hnorm hnormx
  · exact hfix

/-- Select one conjugator for both generation identities and the full-kernel
containment. At least one of its endpoint seeds fails to normalize the
original backward-kernel join. -/
theorem strict_paired_failure_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ q : MixedBackwardShift (h := h) p,
      ∃ x ∈ stabilizer d.radical a,
        Q d.radical q.edge ⊔ Q d.radical (act d.radical x⁻¹ q.edge) = stabilizer d.radical a ∧
        Q d.radical q.edge ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
          stabilizer d.radical a ∧
        Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) ≤
          Q d.radical (act d.radical x (p.walk.getVert 2)) ∧
        (¬ Z d.radical z ≤ normalizer
          (((Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)) ⊔
            Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∨
         ¬ Z d.radical (act d.radical x z) ≤ normalizer
          (((Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)) ⊔
            Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) := by
  obtain ⟨q,_,x,hx,hpair,hend,hkernel⟩ :=
    mixed_strict_backward_paired_kernel_knownSimple hb u him p hstrict
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  refine ⟨q,x,hx,hpair,hend,by simpa only [hl] using hkernel,?_⟩
  by_cases hn : Z d.radical z ≤ normalizer
      (((Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)
  · exact Or.inr (paired_normalization_false_knownSimple hb u him p q hstrict x hend hn)
  · exact Or.inl hn

/-- In the original failed-normalization branch, the line already produced
by the backward kernel is the movement of the full endpoint kernel by the
whole midpoint core. It is fixed at the starting vertex but not at the midpoint. -/
theorem failure_line_whole_midpoint_movement_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : MixedBackwardShift (h := h) p)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hbad : ¬ Z d.radical z ≤ normalizer
      (((Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let H := ⁅Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2),
      Z d.radical z ⊓ Q d.radical a⁆
    H = ⁅Z d.radical z ⊓ Q d.radical a,Q d.radical (p.walk.getVert 2)⁆ ∧
      Nat.card H = 2 ∧ H ≤ Z d.radical q.edge ∧
      H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      ¬ H ≤ centralizer
        (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.path.walk.length = 4 := q.path.length_eq_b.trans hb
  have hq2 : q.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let H := ⁅Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2),
    Z d.radical z ⊓ Q d.radical a⁆
  let F := Z d.radical z ⊓ Q d.radical a
  let M := ⁅F,Q d.radical (p.walk.getVert 2)⁆
  obtain ⟨hcard,hedge,hfixed,hseeds⟩ :=
    mixed_backward_failure_line_knownSimple hb u him p q hstrict hbad
  change Nat.card H = 2 at hcard
  have hHM : H ≤ M := by
    dsimp only [H,M,F]
    rw [commutator_comm]
    exact commutator_mono le_rfl inf_le_right
  have hR : d.radical.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
    exact map_mono (plus_le_exceptional.trans
      CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional.symm.le)
  have hMcard : Nat.card M ≤ 2 := by
    have hh := small_critical_kernel_predecessor_card s hc hb2 u hR p
      (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p)
    simpa only [hl] using hh
  have hMQ : M ≤ Z d.radical z := by
    have hQG : Q d.radical (p.walk.getVert 2) ≤ stabilizer d.radical z :=
      Q_le_stabilizer_of_dist_le_two _ _
        ((p.vertex_color (by omega)).mpr (by decide)) p.end_color
        (by rw [p.dist_end,hl])
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hQG.trans (Z_normalized d.radical z)))
  let := finite_Z d.radical z
  let : Finite M := Finite.of_injective (inclusion hMQ) (inclusion_injective _)
  have he : H = M := eq_of_le_of_card_ge hHM (hcard ▸ hMcard)
  refine ⟨he,hcard,hedge,hfixed,?_⟩
  intro hmid
  have hHQ : H ≤ Q d.radical q.edge := by
    intro y hy
    have hh := hedge hy
    rw [Z,if_neg (by simp [q.edge_color])] at hh
    exact (mem_omegaCenter_iff.mp hh).1
  have hback := q.centrality_transfer H hHQ hfixed hmid
  let qr : CriticalPath d.radical (replacementGeometry h d)
      (p.walk.getVert (p.walk.length-2)) q.start := {
    start_color := q.path.end_color
    walk := q.path.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,q.path.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc q.path }
  have hpre : qr.walk.getVert (qr.walk.length-2) = a := by
    change q.path.walk.reverse.getVert (q.path.walk.reverse.length-2) = a
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,hql]
    exact hq2
  have hFQ : F ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    rw [hl]
    apply inf_le_left.trans
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant z p.end_color,
      SimpleGraph.dist_comm,p.dist_end,hl]
    exact hb2
  have hFpre : F ≤ Q d.radical (qr.walk.getVert (qr.walk.length-2)) := by
    rw [hpre]
    exact inf_le_right
  have hnon : H ≠ ⊥ := by intro he; rw [he,card_bot] at hcard; omega
  exact critical_predecessor_kernel_noncentral s hc hb2 qr
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb qr)
    F hFQ hFpre (by simpa only [hl] using hnon) (by simpa only [hl] using hback)

/-- Apply the same-conjugator obstruction to the literal strict mixed
branch of the terminal consumer. The first alternative identifies a full
midpoint-core movement line; the second keeps failure for the conjugate
endpoint on the original full backward kernel. -/
theorem strict_source_obstruction_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ q : MixedBackwardShift (h := h) p,
      ∃ x ∈ stabilizer d.radical (alpha d.radical),
        Q d.radical q.edge ⊔ Q d.radical (act d.radical x⁻¹ q.edge) =
          stabilizer d.radical (alpha d.radical) ∧
        Q d.radical q.edge ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
          stabilizer d.radical (alpha d.radical) ∧
        Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) ≤
          Q d.radical (act d.radical x (p.walk.getVert 2)) ∧
        ((let M := ⁅Z d.radical z ⊓ Q d.radical (alpha d.radical),
            Q d.radical (p.walk.getVert 2)⁆;
          Nat.card M = 2 ∧ M ≤ Z d.radical q.edge ∧
            M ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
            ¬ M ≤ centralizer
              (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical))) ∨
         ¬ Z d.radical (act d.radical x z) ≤ normalizer
          (((Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)) ⊔
            Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set _)) := by
  obtain ⟨q,x,hx,hpair,hend,hkernel,hbad⟩ :=
    strict_paired_failure_knownSimple hb u him p hstrict
  refine ⟨q,x,hx,hpair,hend,hkernel,?_⟩
  rcases hbad with hbad | hbad
  · obtain ⟨he,hcard,hedge,hfixed,hnon⟩ :=
      failure_line_whole_midpoint_movement_knownSimple hb u him p q hstrict hbad
    rw [he] at hcard hedge hfixed hnon
    exact Or.inl ⟨hcard,hedge,hfixed,hnon⟩
  · exact Or.inr hbad


/-- Apply the proved common-kernel transfer to the actual strict mixed
terminal branch. Only the whole residual-core derived bound and its cross
commutator estimate remain; no endpoint-commutator premise is needed. -/
theorem strict_terminal_false_of_whole_core_estimates_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hCcard : Nat.card (⁅⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆,
      ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆ :
        Subgroup (FreeAmalgam d.radical)) ≤ 2)
    (hcross : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2),
      ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆ ≤
      ⁅⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆,
        ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆) : False := by
  obtain ⟨q⟩ := mixed_strict_backward_shift_knownSimple hb u him p hstrict
  have hd := selected_kernel_derived_knownSimple hb u him p q
  exact selected_terminal_false_of_opposite_core_bounds
    (fullSymmetricAction_knownSimple h e hz hn d (by omega))
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) (by omega) p
    (hd.1 ▸ hd.2) hd.1 hCcard hcross

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
