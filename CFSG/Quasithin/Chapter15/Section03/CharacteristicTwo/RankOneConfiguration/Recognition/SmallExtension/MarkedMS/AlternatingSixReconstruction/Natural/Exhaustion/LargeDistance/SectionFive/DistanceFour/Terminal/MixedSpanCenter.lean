module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedSmallKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedSmallRadius

/-!
# The mixed backward seed in the center of its orbit span

The selected edge holomorph agrees with a starting stabilizer element on
its full edge kernel, so the selected backward seed and the old midpoint
seed have the same full orbit span. The midpoint radius identity puts the
entire backward critical kernel in the radius center. Faithfulness on the
endpoint seed identifies that kernel with the selected seed's intersection
with the embedded span center, and the critical image has exact order two.

These are kernel and center statements, retaining both moving covers and
all central attachments. They do not assert that the center lies in the
Baumann subgroup, which would require residual fixation modulo the seed.
Source: MS93 (5.12)(1),(3), printed pp.924--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- Controlled edge transport preserves the full selected orbit span. -/
theorem MixedBackwardShift.span_eq {a z : Vertex d.radical}
    {p : CriticalPath d.radical (replacementGeometry h d) a z}
    (q : MixedBackwardShift (h := h) p) (hb : replacementDistance h d = 4) :
    localZSpan d.radical q.start a = localZSpan d.radical (p.walk.getVert 2) a := by
  let v := p.walk.getVert 2
  let w := act d.radical q.originalActor⁻¹ (act d.radical q.localActor v)
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hv : color d.radical v = false := (p.vertex_color (by omega)).mpr (by decide)
  have hZQ : Z d.radical v ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical v ((replacementGeometry h d).exists_critical v hv)
    rw [(replacementGeometry h d).distance_constant v hv,SimpleGraph.dist_comm,p.dist_start (by omega)]
    exact show 2 < replacementDistance h d by omega
  have hxQ : Z d.radical (act d.radical q.localActor v) ≤ Q d.radical q.edge := by
    rw [Z_act]
    exact ((map_mono hZQ).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (Q_normalized d.radical a ((stabilizer d.radical a).inv_mem q.local_mem)))).trans
        (Q_le_adjacent_h d.radical q.edge_color q.adjacent_start)
  have hZw : Z d.radical q.start = Z d.radical w := by
    rw [←q.start_eq,Z_act]
    change (Z d.radical (act d.radical q.localActor v)).map (MulAut.conj q.edgeActor⁻¹).toMonoidHom =
      Z d.radical (act d.radical q.originalActor⁻¹ (act d.radical q.localActor v))
    conv_rhs => rw [Z_act,inv_inv]
    exact Escape.Propagation.Backward.Products.map_conj_eq_of_agree hxQ q.agreement
  have hspanw : localZSpan d.radical w a = localZSpan d.radical v a := by
    have hxfix : act d.radical q.localActor a = a := q.local_mem
    have hgfix : act d.radical q.originalActor⁻¹ a = a :=
      (stabilizer d.radical a).inv_mem q.original_mem
    have hxP : (localZSpan d.radical v a).map (MulAut.conj q.localActor⁻¹).toMonoidHom =
        localZSpan d.radical v a := mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized d.radical v a ((stabilizer d.radical a).inv_mem q.local_mem))
    have hgP : (localZSpan d.radical (act d.radical q.localActor v) a).map
        (MulAut.conj q.originalActor).toMonoidHom =
        localZSpan d.radical (act d.radical q.localActor v) a := mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized d.radical _ a q.original_mem)
    have he₁ := LocalCommutator.CriticalCase.localZSpan_act (R := d.radical)
      q.originalActor⁻¹ (act d.radical q.localActor v) a
    have he₂ := LocalCommutator.CriticalCase.localZSpan_act (R := d.radical) q.localActor v a
    rw [hgfix,inv_inv,hgP] at he₁
    rw [hxfix,hxP] at he₂
    exact he₁.trans he₂
  have seed_span {c t : Vertex d.radical} (he : Z d.radical c = Z d.radical t) :
      localZSpan d.radical c a = localZSpan d.radical t a := by
    simp only [localZSpan_eq_conjugates,he]
  exact (seed_span hZw).trans hspanw

/-- The full selected kernel is exactly the seed's intersection with the
embedded center of its orbit span. -/
theorem MixedBackwardShift.kernel_eq_center_intersection
    {a z : Vertex d.radical}
    {p : CriticalPath d.radical (replacementGeometry h d) a z}
    (q : MixedBackwardShift (h := h) p) (hb : replacementDistance h d = 4)
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (hKC : Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) ≤
      centralizer (localZSpan d.radical (p.walk.getVert 2) a : Set (FreeAmalgam d.radical))) :
    Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) =
      Z d.radical q.start ⊓
        (center (localZSpan d.radical (p.walk.getVert 2) a)).map
          (localZSpan d.radical (p.walk.getVert 2) a).subtype := by
  let P := localZSpan d.radical (p.walk.getVert 2) a
  have hZP : Z d.radical q.start ≤ P := by
    rw [show P=localZSpan d.radical (p.walk.getVert 2) a from rfl,←q.span_eq hb]
    exact Z_le_localZSpan d.radical _ _
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hv : color d.radical (p.walk.getVert 2) = false := (p.vertex_color (by omega)).mpr (by decide)
  have hZG : Z d.radical q.start ≤ stabilizer d.radical (p.walk.getVert 2) := by
    have hh := critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (p.walk.getVert (p.walk.length-2)) q.path.end_color
      (by rw [(replacementGeometry h d).distance_constant _ q.path.end_color];
          exact replacementDistance_pos h d) (critical_reverse_pair s hc q.path)
    simpa only [hl] using hh
  apply le_antisymm
  · apply le_inf inf_le_left
    intro y hy
    refine ⟨⟨y,hZP hy.1⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact hKC hy x x.property
  · apply le_inf inf_le_left
    intro y hy
    rw [←C_eq_Q s hc _ hv]
    refine ⟨hZG hy.1,?_⟩
    obtain ⟨c,hc',rfl⟩ := hy.2
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp hc' ⟨x,Z_le_localZSpan d.radical _ _ hx⟩)

/-- The midpoint-radius identity puts the full backward kernel in the
center of the whole radius, before passing to the selected orbit span. -/
theorem mixed_backward_kernel_centralizes_radius_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : MixedBackwardShift (h := h) p) :
    Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) ≤
      centralizer (V d.radical a : Set (FreeAmalgam d.radical)) := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hq2 : q.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have he := (mixed_midpoint_radius_data_knownSimple hb u him q.path).2.2.2
  rw [hq2,hl] at he
  exact he.ge.trans inf_le_right

/-- The selected seed has exact image order two modulo the center of its
full orbit span, and its full critical kernel lies in the radius center. -/
theorem mixed_backward_kernel_center_data_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : MixedBackwardShift (h := h) p) :
    let P := localZSpan d.radical (p.walk.getVert 2) a
    let K := Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)
    let C := (center P).map P.subtype
    Z d.radical q.start ≤ P ∧ K = Z d.radical q.start ⊓ C ∧
      C.relIndex (Z d.radical q.start) = 2 ∧
      K ≤ (center (V d.radical a)).map (V d.radical a).subtype := by
  let P := localZSpan d.radical (p.walk.getVert 2) a
  let K := Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)
  let C := (center P).map P.subtype
  have hZP : Z d.radical q.start ≤ P := by
    rw [show P=localZSpan d.radical (p.walk.getVert 2) a from rfl,←q.span_eq hb]
    exact Z_le_localZSpan d.radical _ _
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hPV : P ≤ V d.radical a := localZSpan_le_V d.radical
    (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  have hKC := mixed_backward_kernel_centralizes_radius_knownSimple hb u him p q
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have he : K = Z d.radical q.start ⊓ C :=
    q.kernel_eq_center_intersection hb s hc (hKC.trans (centralizer_le hPV))
  refine ⟨hZP,he,?_,?_⟩
  · have hi := (small_critical_indices s hc q.path
      (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q.path)).1
    change (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical q.start) = 2 at hi
    rw [hl] at hi
    rw [←inf_relIndex_left,←he]
    simpa only [K,inf_relIndex_left] using hi
  · intro y hy
    refine ⟨⟨y,hPV (hZP hy.1)⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact hKC hy x x.property

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
