module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.MarkedResidualLine
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.OppositeNoncentral

/-!
# The opposite slice of a strict mixed source path

A small opposite slice fixes the whole predecessor-core movement at the
conjugate midpoint. The actual marked failure line lies in that midpoint's
full seed and is already fixed by the starting stabilizer. Thus the source
residual-fixed estimate applies to its full omega layer, without discarding
central attachments or inferring omega membership from an unrelated seed.

Source: MS93 (5.12)(3), printed pp.926--927.
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

/-- A small opposite slice fixes the actual marked conjugate failure line
at its own midpoint. The marking and full seed placement are proved inputs
of the actual selected source witness. -/
theorem conjugate_small_opposite_failure_fixed_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : MixedBackwardShift (h := h) p)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (hmark : x ∈ normalizer (Z d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)))
    (hbad : ¬ Z d.radical (act d.radical x z) ≤ normalizer
      (((Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2))) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hopposite : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2) :
    ⁅Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2)),
      Z d.radical (act d.radical x z) ⊓ Q d.radical a⁆ ≤
        centralizer (stabilizer d.radical (act d.radical x (p.walk.getVert 2)) :
          Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hxa : act d.radical x a = a := hx
  have hv : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨_,_,hfix,hseeds⟩ :=
    conjugate_failure_line_fixed_knownSimple hb u him p q hstrict x hx hmark hbad
  let H := ⁅Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2)),
    Z d.radical (act d.radical x z) ⊓ Q d.radical a⁆
  change H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) at hfix
  change H ≤ Z d.radical q.start ⊓ Z d.radical (p.walk.getVert 2) ⊓
    Z d.radical (act d.radical x z) at hseeds
  have hHz : H ≤ Z d.radical (act d.radical x (p.walk.getVert 2)) :=
    (fixed_line_le_seed_iff_conjugate H hfix x hx).mpr
      (hseeds.trans (inf_le_left.trans inf_le_right))
  have hvx : color d.radical (act d.radical x (p.walk.getVert 2)) = false := (action_preserves_color d.radical _ _).trans hv
  have hHX : H ≤ X d.radical (act d.radical x (p.walk.getVert 2)) := hHz.trans
    ((replacementGeometry h d).omega_bound _ hvx (by
      rw [(replacementGeometry h d).distance_constant _ hvx]
      exact replacementDistance_pos h d))
  have hopx : (B d.radical ((p.act x).walk.getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (act d.radical x z)) ≤ 2 := by
    simp only [CriticalPath.act,actWalk_getVert]
    rw [Escape.PairingControl.FirstPairing.B_act (geometry := replacementGeometry h d)
      hb2 x (p.walk.getVert 2) hv,U_act,
      relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hopposite
  have hwhole := small_predecessor_whole_core_fixed s hc hb (p.act x) hopx
  simp only [CriticalPath.act,actWalk_getVert,hxa] at hwhole
  have hfixed : H ≤ fixedCore d.radical (act d.radical x (p.walk.getVert 2)) := by
    change ⁅_,_⁆ ≤ _
    rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans hwhole
  have hsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb (p.act x)
  exact (le_inf hHX hfixed).trans
    (omega_fixed_central_of_small_critical s hc (p.act x) hsmall _ hvx)

/-- A strict forward mixed slice forces the opposite slice to be strict.
The same marked source pair supplies both normalization attempts; midpoint
fixation in the small-slice case contradicts full-kernel noncentrality. -/
theorem strict_opposite_slice_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) := by
  by_contra! hopposite
  obtain ⟨q,x,hxL,_,hend,hkernel,hmark,_⟩ :=
    strict_selected_marked_residual_pair_knownSimple hb u him p hstrict
  have hx := Ltilde_le_stabilizer (alpha d.radical) hxL
  have hnorm := mixed_small_backward_kernel_normalized_of_opposite_slice_knownSimple
    hb u him p q hstrict hopposite
  have hbad : ¬ Z d.radical (act d.radical x z) ≤ normalizer
      (((Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2))) ⊔
        Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hh
    exact paired_normalization_false_knownSimple hb u him p q hstrict x hend hnorm
      (backward_kernel_normalization_transfer_knownSimple hb u him p q _ _
        (le_inf inf_le_left hkernel) inf_le_left (le_sup_right.trans_eq hend) hh)
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hvt : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hf : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hinter := mixed_strict_seed_intersection_eq_edge s (by omega) u hf
    p.start_color hat hvt hstrict
  rw [hinter] at hmark
  obtain ⟨hcard,hedge,hfixa,_⟩ :=
    conjugate_failure_line_fixed_knownSimple hb u him p q hstrict x hx hmark hbad
  have hfixmid := conjugate_small_opposite_failure_fixed_knownSimple
    hb u him p q hstrict x hx hmark hbad hopposite
  exact conjugate_failure_line_not_fixed_knownSimple (e := e) (hz := hz) (hn := hn)
    hb p q x hx hcard hedge hfixa hfixmid

/-- Strict mixed slices propagate on every component vertex of the same
original graph. -/
theorem strict_opposite_slice_at_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := strict_opposite_slice_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u him (z := act d.radical g⁻¹ z)
  rw [←hbase] at base
  have hs : 2 < (B d.radical (act d.radical g⁻¹ a)
      ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical ((p.act g⁻¹).walk.getVert 2)) := by
    change 2 < (B d.radical _ _).relIndex
      (U d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2))
    rw [actWalk_getVert,Escape.PairingControl.FirstPairing.B_act hb2 _ _ p.start_color,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hstrict
  have hi := base (p.act g⁻¹) hs
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hi' : 2 < (B d.radical (act d.radical g⁻¹ (p.walk.getVert 2))
      ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical g⁻¹ z)) := by
    simpa only [CriticalPath.act,actWalk_getVert] using hi
  rwa [Escape.PairingControl.FirstPairing.B_act hb2 _ _ hcol,
    U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective] at hi'

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
