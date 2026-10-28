module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedPairedGeneration
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedSmallRadius
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedConjugateKernel

/-!
# A common mixed backward kernel at distance four

The reversed selected path gives radius index two at its endpoint. All
escaping seeds in that radius therefore give the same commutator line.
The paired edge generation makes this line central at the midpoint, and
conjugation transports it to the second endpoint. Small critical pairs
with the same line have the same full kernel, retaining both central covers.

Source: MS93 (5.12)(1),(3), printed pp.924--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
open MixedConjugateKernel
local notation "S" => Equiv.Perm (Fin 6)
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem mixed_four_near_critical
    (hb : replacementDistance h d = 4)
    {a a' z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hz : color d.radical z = false)
    (hnear : (cosetGraph d.radical).dist z a ≤ 2)
    (hout : ¬ Z d.radical z ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    Nonempty (CriticalPath d.radical (replacementGeometry h d) z
      (p.walk.getVert (p.walk.length-2))) := by
  let c := p.walk.getVert (p.walk.length-2)
  have hpair : CriticalPair d.radical z c ((replacementGeometry h d).exists_critical z hz) := by
    refine ⟨?_,hout⟩
    apply le_antisymm _ (criticalDistance_le d.radical z _ hout)
    rw [(replacementGeometry h d).distance_constant z hz]
    have ht := (cosetGraph_connected d.radical).dist_triangle (u := z) (v := a) (w := c)
    have hac : (cosetGraph d.radical).dist a c = p.walk.length-2 :=
      p.dist_start (Nat.sub_le _ _)
    have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    change (cosetGraph d.radical).dist z c ≤ replacementDistance h d
    omega
  exact ⟨CriticalPath.ofPair (geometry := replacementGeometry h d) hz hpair⟩

private theorem mixed_four_near_seed_radius_commutator
    (hb : replacementDistance h d = 4)
    {a a' z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hradius : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (V d.radical a) = 2)
    (q : CriticalPath d.radical (replacementGeometry h d) z
      (p.walk.getVert (p.walk.length-2)))
    (hnear : (cosetGraph d.radical).dist z a ≤ 2) :
    ⁅V d.radical a,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ =
      ⁅Z d.radical z,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ := by
  let c := p.walk.getVert (p.walk.length-2)
  let W := V d.radical a
  have hi := hradius
  have hZ : Z d.radical z ≤ W := le_iSup_of_le z (le_iSup_of_le hnear le_rfl)
  have hWG : W ≤ stabilizer d.radical c := by
    apply (V_le_iff d.radical p.start_color _).mpr
    intro v hv hva
    apply Z_le_stabilizer_of_dist_le v _
    rw [(replacementGeometry h d).distance_constant v hv]
    have hac : (cosetGraph d.radical).dist a c = p.walk.length-2 :=
      p.dist_start (Nat.sub_le _ _)
    have ht := (cosetGraph_connected d.radical).dist_triangle (u := v) (v := a) (w := c)
    have hl : p.walk.length=replacementDistance h d := p.length_eq_b
    change _ ≤ replacementDistance h d
    omega
  have hQ : Q d.radical c ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical c q.end_color))
  exact commutator_eq_of_centralizing_index_two (Z d.radical c) (W ⊓ Q d.radical c) W
    (Z d.radical z) (hWG.trans (Z_normalized d.radical c)) inf_le_left
    (inf_le_right.trans hQ) (by simpa only [inf_relIndex_left] using hi)
    hZ (fun he => q.critical.2 (he.trans inf_le_right))

/-- If both conjugate backward seeds escape the predecessor core, their
whole-radius line is fixed by the entire intermediate stabilizer. The
extra generation hypothesis concerns the two literal edge kernels. -/
theorem mixed_four_generating_conjugate_common_line_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' z t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) z
      (p.walk.getVert (p.walk.length-2)))
    (hradius : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (V d.radical a) = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (hgen : Q d.radical t ⊔ Q d.radical (act d.radical x⁻¹ t) = stabilizer d.radical a)
    (hout : ¬ Z d.radical (act d.radical x⁻¹ z) ≤
      Q d.radical (p.walk.getVert (p.walk.length-2))) :
    let c := p.walk.getVert (p.walk.length-2)
    ⁅Z d.radical z,Z d.radical c⁆ = ⁅Z d.radical (act d.radical x⁻¹ z),Z d.radical c⁆ ∧
      ⁅V d.radical a,Z d.radical c⁆ ≤
        centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let c := p.walk.getVert (p.walk.length-2)
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hnear := edge_near hat hzt
  have hfix : act d.radical x⁻¹ a = a := (stabilizer d.radical a).inv_mem hx
  have hnear' : (cosetGraph d.radical).dist (act d.radical x⁻¹ z) a ≤ 2 := by
    rw [←hfix,dist_act]
    exact hnear
  have hw : color d.radical (act d.radical x⁻¹ z) = false := by
    rw [action_preserves_color,q.start_color]
  obtain ⟨r⟩ := mixed_four_near_critical hb p hw hnear' hout
  have heq := (mixed_four_near_seed_radius_commutator hb p hradius q hnear).symm.trans
    (mixed_four_near_seed_radius_commutator hb p hradius r hnear')
  refine ⟨heq,?_⟩
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
    exact map_mono plus_le_D
  have hcQa : Z d.radical c ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c q.end_color)
    rw [(replacementGeometry h d).distance_constant c q.end_color,SimpleGraph.dist_comm]
    have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    change (cosetGraph d.radical).dist a c < replacementDistance h d
    rw [p.dist_start (Nat.sub_le _ _)]
    omega
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases he : color d.radical t <;> simp_all
  have hcQt : Z d.radical c ≤ Q d.radical t := hcQa.trans (Q_le_adjacent_h d.radical ht hat)
  have hQmap : (Q d.radical a).map (MulAut.conj x).toMonoidHom = Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hx)
  have hcQt' : Z d.radical c ≤ Q d.radical (act d.radical x⁻¹ t) := by
    rw [Q_act,inv_inv]
    exact hcQa.trans (hQmap ▸ map_mono (Q_le_adjacent_h d.radical ht hat))
  have hline : ⁅Z d.radical z,Z d.radical c⁆ ≤ Z d.radical t :=
    (commutator_mono le_rfl hcQt).trans (cube_edge_seed_commutator_le s hc u hR q.start_color hzt)
  have hline' : ⁅Z d.radical z,Z d.radical c⁆ ≤ Z d.radical (act d.radical x⁻¹ t) := by
    rw [heq]
    exact (commutator_mono le_rfl hcQt').trans
      (cube_edge_seed_commutator_le s hc u hR hw ((adjacent_act_iff d.radical x⁻¹ _ _).mpr hzt))
  have hseed (v : Vertex d.radical) (hv : color d.radical v = true) :
      Z d.radical v ≤ centralizer (Q d.radical v : Set (FreeAmalgam d.radical)) := by
    intro y hy
    rw [Z,if_neg (by simp [hv])] at hy
    exact (mem_omegaCenter_iff.mp hy).2.2
  rw [mixed_four_near_seed_radius_commutator hb p hradius q hnear]
  apply le_centralizer_iff.mp
  rw [←hgen]
  exact sup_le (le_centralizer_iff.mp (hline.trans (hseed t ht)))
    (le_centralizer_iff.mp (hline'.trans (hseed _ (by rw [action_preserves_color,ht]))))

/-- The entire backward seed kernel lies in the conjugated predecessor
core. The escaping case uses the whole intermediate stabilizer's fixed
line; the trapped case follows directly, with all central attachments. -/
theorem mixed_four_generating_conjugate_kernel_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' z t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) z
      (p.walk.getVert (p.walk.length-2)))
    (hradius : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (V d.radical a) = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (hgen : Q d.radical t ⊔ Q d.radical (act d.radical x⁻¹ t) = stabilizer d.radical a) :
    Z d.radical z ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)) ≤
      Q d.radical (act d.radical x (p.walk.getVert (p.walk.length-2))) := by
  let c := p.walk.getVert (p.walk.length-2)
  let w := act d.radical x⁻¹ z
  have hcancel : act d.radical x w = z := by
    dsimp only [w]
    rw [←act_mul,inv_mul_cancel,act_one]
  by_cases hout : Z d.radical w ≤ Q d.radical c
  · have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hout
    rw [←Z_act,←Q_act,hcancel] at hh
    exact inf_le_left.trans hh
  have hline := mixed_four_generating_conjugate_common_line_knownSimple hb u him p q hradius hat hzt x hx hgen hout
  have hnear := edge_near hat hzt
  have hfix : act d.radical x⁻¹ a = a := (stabilizer d.radical a).inv_mem hx
  have hnear' : (cosetGraph d.radical).dist w a ≤ 2 := by
    rw [show w = act d.radical x⁻¹ z from rfl,←hfix,dist_act]
    exact hnear
  have hw : color d.radical w = false := (action_preserves_color d.radical _ _).trans q.start_color
  obtain ⟨r⟩ := mixed_four_near_critical hb p hw hnear' hout
  obtain ⟨r'⟩ : Nonempty (CriticalPath d.radical (replacementGeometry h d) z (act d.radical x c)) := by
    rw [←hcancel]
    exact ⟨r.act x⟩
  let H := ⁅Z d.radical z,Z d.radical c⁆
  have hHC : H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    change ⁅Z d.radical z,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤ _
    rw [←mixed_four_near_seed_radius_commutator hb p hradius q hnear]
    exact hline.2
  have hHmap : H.map (MulAut.conj x⁻¹).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _ ((le_centralizer_iff.mp hHC)
        ((stabilizer d.radical a).inv_mem hx)))
  have heq : ⁅Z d.radical z,Z d.radical c⁆ = ⁅Z d.radical z,Z d.radical (act d.radical x c)⁆ := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hline.1
    change H.map (MulAut.conj x⁻¹).toMonoidHom = _ at hh
    rw [hHmap,map_commutator,←Z_act,←Z_act,hcancel] at hh
    exact hh
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hq : (Q d.radical c).relIndex (Z d.radical z) < 4 :=
    critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q
  have hr : (Q d.radical (act d.radical x c)).relIndex (Z d.radical z) < 4 :=
    critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb r'
  exact (small_critical_equal_commutators_kernel s hc q r' hq hr heq).le.trans inf_le_right

include e hz hn in
/-- The literal backward path supplies the radius index needed by the
common-line argument, by reversal through its actual midpoint. -/
theorem mixed_four_backward_radius_index_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : CriticalPath d.radical (replacementGeometry h d) c
      (p.walk.getVert (p.walk.length-2)))
    (hq2 : q.walk.getVert 2 = a) :
    (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (V d.radical a) = 2 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let qr : CriticalPath d.radical (replacementGeometry h d)
      (p.walk.getVert (p.walk.length-2)) c := {
    start_color := q.end_color
    walk := q.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc q }
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hr2 : qr.walk.getVert 2 = a := by
    change q.walk.reverse.getVert 2 = a
    rw [SimpleGraph.Walk.getVert_reverse,hql]
    exact hq2
  have hd := (mixed_midpoint_radius_data_knownSimple hb u him qr).1
  rwa [hr2] at hd

include e hz hn in
/-- Both paired generation equalities and the full kernel containment hold
for one selected strict backward path. The radius premise is discharged by
that same path; no equality of independently selected kernels is assumed. -/
theorem mixed_strict_backward_paired_kernel_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ q : MixedBackwardShift (h := h) p,
      2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical q.start) ∧
      ∃ x ∈ stabilizer d.radical a,
        Q d.radical q.edge ⊔ Q d.radical (act d.radical x⁻¹ q.edge) = stabilizer d.radical a ∧
        Q d.radical q.edge ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
          stabilizer d.radical a ∧
        Z d.radical q.start ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)) ≤
          Q d.radical (act d.radical x (p.walk.getVert (p.walk.length-2))) := by
  obtain ⟨q,hq,x,hx,hpair,hend⟩ := mixed_strict_backward_paired_generation_knownSimple hb u him p hstrict
  have hpl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hq2 : q.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (by omega)
  have hct : Adjacent d.radical q.start q.edge := by
    have hql : q.path.walk.length = 4 := q.path.length_eq_b.trans hb
    have hh := q.path.walk.adj_getVert_succ (i := 0) (by omega)
    simpa only [SimpleGraph.Walk.getVert_zero,Nat.zero_add,q.first] using
      (cosetGraph_adj d.radical _ _).mp hh
  refine ⟨q,hq,x,hx,hpair,hend,?_⟩
  exact mixed_four_generating_conjugate_kernel_knownSimple hb u him p q.path
    (mixed_four_backward_radius_index_knownSimple hb u him p q.path hq2)
    q.adjacent_start hct x hx hpair

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
