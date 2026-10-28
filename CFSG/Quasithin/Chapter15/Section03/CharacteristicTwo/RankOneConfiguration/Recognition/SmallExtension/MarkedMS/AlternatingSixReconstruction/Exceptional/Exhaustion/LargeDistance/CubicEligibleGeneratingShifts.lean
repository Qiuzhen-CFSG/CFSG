module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLargeShifts
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneEscape
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneCoreAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalShifts

/-!
# Eligible generating shifts on the original cubic plane graph

An eligible neighbor suffices for the controlled large-image backward
construction. If its full seed lay in the predecessor core, the controlled
actor and the selected edge would normalize its seed supplement and put
that supplement in the Baumann slice. This contradicts eligibility directly.
The original transporter, full seed, cubic kernel E and every overlap are kept.

In the plane branch quadratic full-seed action places every critical
commutator in its first edge seed. Above distance four two successive
single-endpoint generating backward shifts are impossible. Consequently
any such shift has both critical indices and commutator order two.
The original radius-escape theorem constructs one for every large image.

Only the general critical-commutator transport theorem from OriginalSylow
is reused; its signature has no Sylow or radical-image hypothesis.
This module does not exclude all large images or distances above four.

Source: MS93 (5.7)--(5.11), printed pp.919--924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz in
private theorem eligible_controlled_actor_backward_not_le
    (hb : 2 < sourceDistance h)
    {a' c t : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (A : Subgroup (FreeAmalgam Rg)) (hAG : A ≤ stabilizer Rg (alpha Rg))
    (htwo : IsPGroup 2 A) (hAn : ¬ A ≤ Q Rg (alpha Rg))
    (hdisp : ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert (p.walk.length-2)),A⁆ ≤ Z Rg (alpha Rg))
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : Q Rg t ⊔ A = stabilizer Rg (alpha Rg))
    (heligible : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    ¬ Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  let D := Z Rg c ⊔ Z Rg (alpha Rg)
  have hDV : D ≤ V Rg (alpha Rg) :=
    CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hct
  have hVG : V Rg (alpha Rg) ≤ stabilizer Rg (alpha Rg) :=
    (sourceGeometry h).V_local _ rfl hb
  have hDA : ⁅D,A⁆ ≤ Z Rg (alpha Rg) := by
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      (Z Rg c) (Z Rg (alpha Rg)) A (Z Rg (alpha Rg))
      (Z_normalized Rg _) ((le_sup_left.trans hDV).trans hVG) (Z_le_stabilizer Rg _)
    · exact (commutator_mono (le_inf (le_sup_left.trans hDV) hbad) le_rfl).trans hdisp
    · exact le_normalizer_iff_commutator_le_left.mp (hAG.trans (Z_normalized Rg _))
  have hDN : stabilizer Rg (alpha Rg) ≤ normalizer (D : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hat hct)
      (le_normalizer_iff_commutator_le_left.mpr (hDA.trans le_sup_right))
  have hDB := normalized_radius_le_slice_of_controlled_actor h e hz hb rfl D A
    hDV hDN hAG htwo hAn hDA
  have hUB : U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    (DistanceEight.U_le_Z Rg c).trans (le_sup_left.trans hDB)
  exact heligible hUB

include h e hz hk in
/-- The controlled backward construction needs only failure of containment
in the starting Baumann slice. The old strict-index premise is discharged. -/
theorem large_remaining_backward_shift_of_eligible
    (hb : 2 < sourceDistance h)
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a' delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg)))
    (hdelta : Adjacent Rg delta (p.walk.getVert 1))
    (heligible : ¬ U Rg delta ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
      ∃ g ∈ stabilizer Rg (alpha Rg),
      act Rg g (p.walk.getVert 1) = t ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g delta)
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        ¬ U Rg (act Rg g delta) ≤
          B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  obtain ⟨A,hAU,htwo,hAn,hdisp,t,hat,hgen⟩ :=
    large_remaining_generating_actor h e hz hk u hR p hlarge
  have hAZ : A ≤ Z Rg a' := hAU.trans (DistanceEight.U_le_Z Rg a')
  have hZG : Z Rg a' ≤ stabilizer Rg (alpha Rg) :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have ha1 : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) ha1 hat
  let c := act Rg g delta
  have hct : Adjacent Rg c t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g delta (p.walk.getVert 1)).mpr hdelta
  have hcol : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    change false ≠ color Rg t at h1
    cases hc : color Rg c <;> cases ht : color Rg t <;> simp_all
  have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hg))
  have helc : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
    intro hh
    apply heligible
    change U Rg (act Rg g delta) ≤ _ at hh
    rw [U_act,←hB] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
  have hbad : ¬ Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    exact eligible_controlled_actor_backward_not_le h e hz hb p A (hAZ.trans hZG) htwo hAn hdisp hat hct hgen helc
  let w : (cosetGraph Rg).Walk c (alpha Rg) :=
    .cons ((cosetGraph_adj Rg _ _).mpr hct)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (Nat.le_of_lt hb) hcol w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  refine ⟨t,hat,?_,g,hg,hgt,q,hqt,fun i hi => p.prepend_two_overlap _ _ _ _ _ hi,helc⟩
  exact le_antisymm (sup_le (le_sup_left.trans hgen.le) hZG)
    (hgen.symm.le.trans (sup_le_sup_left hAZ _))

/-- One literal generating backward shift, including its transporter and
all retained vertices. No Sylow assumption is part of this structure. -/
structure GeneratingBackwardShift {a z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z) where
  start : Vertex Rg
  edge : Vertex Rg
  transporter : FreeAmalgam Rg
  transporter_mem : transporter ∈ stabilizer Rg a
  first_eq : act Rg transporter (p.walk.getVert 1) = edge
  start_eq : act Rg transporter (p.walk.getVert 2) = start
  adjacent_start : Adjacent Rg a edge
  adjacent_shift : Adjacent Rg start edge
  generation : Q Rg edge ⊔ Z Rg z = stabilizer Rg a
  path : CriticalPath Rg (sourceGeometry h) start (p.walk.getVert (p.walk.length-2))
  first : path.walk.getVert 1 = edge
  overlap : ∀ i ≤ p.walk.length-2, path.walk.getVert (i+2) = p.walk.getVert i

include h e hz hk in
private theorem plane_large_backward_step_base
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    ∃ c t x, x ∈ stabilizer Rg (alpha Rg) ∧
      act Rg x (p.walk.getVert 1) = t ∧
      act Rg x (p.walk.getVert 2) = c ∧
      Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) c
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) := by
  have hb := distance_gt_two h e hz hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hdelta : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,hgen,x,hx,hxt,q,hqt,hover,_⟩ :=
    large_remaining_backward_shift_of_eligible h e hz hk hb u (Or.inl hR) p hlarge
      hdelta (plane_critical_paths h e hz hk u hR p).2.2.2
  refine ⟨_,t,x,hx,hxt,rfl,hat,?_,hgen,q,hqt,hover⟩
  rw [←hxt]
  exact (adjacent_act_iff Rg x _ _).mpr hdelta

include h e hz hk in
/-- Every original plane critical path with large image has a generating
backward shift, with no strict-slice or eligibility assumption. -/
private theorem plane_large_backward_step_at
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg a)) :
    ∃ c t x, x ∈ stabilizer Rg a ∧
      act Rg x (p.walk.getVert 1) = t ∧
      act Rg x (p.walk.getVert 2) = c ∧
      Adjacent Rg a t ∧ Adjacent Rg c t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg a ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) c
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := plane_large_backward_step_base h e hz hk u hR
    (z := act Rg g⁻¹ a')
  rw [←hbase] at base
  obtain ⟨c,t,x,hx,hxt,hxc,hat,hct,hgen,q,hq1,hover⟩ := base (p.act g⁻¹) (by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge)
  change act Rg x ((actWalk Rg g⁻¹ p.walk).getVert 2) = c at hxc
  change act Rg x ((actWalk Rg g⁻¹ p.walk).getVert 1) = t at hxt
  rw [actWalk_getVert] at hxc hxt
  let y := g⁻¹*x*g
  have hy (v : Vertex Rg) :
      act Rg y v = act Rg g (act Rg x (act Rg g⁻¹ v)) := by
    simp only [y,act_mul]
  have hcancel (v : Vertex Rg) : act Rg g (act Rg g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hqc : ∃ r : CriticalPath Rg (sourceGeometry h)
      (act Rg g c)
      (act Rg g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2))),
      r.walk.getVert 1 = act Rg g t ∧
      ∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i := by
    refine ⟨q.act g,?_,?_⟩
    · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act Rg g) hq1
    · intro i hi
      have he := congrArg (act Rg g) (hover i (by
        simpa only [CriticalPath.act,actWalk_length] using hi))
      simpa only [CriticalPath.act,actWalk_getVert,hcancel] using he
  have hend : act Rg g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2)) =
      p.walk.getVert (p.walk.length-2) := by
    change act Rg g ((actWalk Rg g⁻¹ p.walk).getVert
      ((actWalk Rg g⁻¹ p.walk).length-2)) = _
    rw [actWalk_length,actWalk_getVert,hcancel]
  rw [hend] at hqc
  obtain ⟨r,hr1,hrover⟩ := hqc
  refine ⟨act Rg g c,act Rg g t,y,?_,?_,?_,?_,?_,?_,r,hr1,hrover⟩
  · change act Rg y a = a
    rw [hy,show act Rg x (act Rg g⁻¹ a) = act Rg g⁻¹ a from hx,hcancel]
  · rw [hy,hxt]
  · rw [hy,hxc]
  · simpa only [hcancel] using (adjacent_act_iff Rg g _ _).mpr hat
  · exact (adjacent_act_iff Rg g _ _).mpr hct
  · have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hcancel,hcancel] at he
    exact he

include h e hz hk in
/-- The actual large-image generating shift at any original component vertex. -/
theorem plane_large_generating_backward_shift
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg a)) :
    Nonempty (GeneratingBackwardShift h p) := by
  obtain ⟨c,t,x,hx,hxt,hxc,hat,hct,hgen,q,hq1,hover⟩ :=
    plane_large_backward_step_at h e hz hk u hR p hlarge
  exact ⟨⟨c,t,x,hx,hxt,hxc,hat,hct,hgen,q,hq1,hover⟩⟩

include h e hz hk in
/-- Quadraticity of the original plane edge places every full critical
commutator in its first edge seed, even for a large critical image. -/
theorem plane_critical_commutator_le_first_seed
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    ⁅Z Rg a,Z Rg z⁆ ≤ Z Rg (p.walk.getVert 1) := by
  have hl : 0 < p.walk.length := p.length_eq_b ▸ sourceDistance_pos h
  have hat : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hZe : Z Rg z ≤ Q Rg (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt Rg z ((sourceGeometry h).exists_critical z p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(sourceGeometry h).distance_constant z p.end_color]
    have he : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length - 1 < sourceDistance h
    omega
  exact (commutator_mono le_rfl hZe).trans
    (plane_edge_seed_commutator h e hz hk u hR p.start_color hat)

include h e hz hk in
/-- Two successive generating backward shifts are impossible above distance
four in the original plane graph. Both generating equations are used. -/
theorem plane_two_generating_backward_shifts_false
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : GeneratingBackwardShift h p) (r : GeneratingBackwardShift h q.path) : False := by
  have hq2 : q.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have hyz : act Rg r.transporter a = r.start := by
    simpa only [hq2] using r.start_eq
  have hlenP : p.walk.length = sourceDistance h := p.length_eq_b
  have hlenQ : q.path.walk.length = sourceDistance h := q.path.length_eq_b
  have hdist1 : (cosetGraph Rg).dist (q.path.walk.getVert (q.path.walk.length-2))
      (p.walk.getVert (p.walk.length-2)) = 2 := by
    rw [q.path.dist_end]
    omega
  have hdist2 : (cosetGraph Rg).dist (p.walk.getVert (p.walk.length-2)) a' = 2 := by
    rw [p.dist_end]
    omega
  have hdist : (cosetGraph Rg).dist (q.path.walk.getVert (q.path.walk.length-2)) a' ≤ 4 := by
    have hh := (cosetGraph_connected Rg).dist_triangle
      (u := q.path.walk.getVert (q.path.walk.length-2)) (v := p.walk.getVert (p.walk.length-2)) (w := a')
    omega
  let H := ⁅Z Rg r.start,Z Rg (q.path.walk.getVert (q.path.walk.length-2))⁆
  have hHe : H ≤ Z Rg (q.path.walk.getVert (q.path.walk.length-2)) :=
    le_normalizer_iff_commutator_le_right.mp
      ((Z_le_stabilizer_of_dist_le r.start _ r.path.critical.1.le).trans
        (Z_normalized Rg _))
  have hcent (w : Vertex Rg) (hw : color Rg w = false)
      (hdist : (cosetGraph Rg).dist (q.path.walk.getVert (q.path.walk.length-2)) w < sourceDistance h) :
      H ≤ centralizer (Z Rg w : Set (FreeAmalgam Rg)) := by
    apply (hHe.trans (Z_le_Q_of_dist_lt Rg _
      ((sourceGeometry h).exists_critical _ r.path.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg w hw)))
    rwa [(sourceGeometry h).distance_constant _ r.path.end_color]
  have hnc := AlternatingSixReconstruction.Exceptional.OriginalSylow.critical_commutator_not_central_at_shift_vertex h e hz hk r.path
    q.start q.edge a a' (by rw [r.first]; exact r.adjacent_start)
    q.adjacent_shift q.generation (hcent _ p.end_color (by omega)) r.transporter r.transporter_mem hyz
  have hHt : H ≤ Z Rg r.edge := by
    simpa only [r.first] using plane_critical_commutator_le_first_seed h e hz hk u hR r.path
  have ht : color Rg r.edge = true := by
    have hh := adjacent_color_ne Rg r.adjacent_start
    rw [q.path.start_color] at hh
    cases he : color Rg r.edge <;> simp_all
  have hHQ : H ≤ centralizer (Q Rg r.edge : Set (FreeAmalgam Rg)) := by
    intro x hx
    have hh := hHt hx
    rw [Z,if_neg (by simp [ht])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  apply hnc
  change H ≤ centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg))
  apply le_centralizer_iff.mp
  rw [←r.generation]
  exact sup_le (le_centralizer_iff.mp hHQ)
    (le_centralizer_iff.mp (hcent _ q.path.end_color (by omega)))

include h e hz hk in
/-- Every generating backward shift above distance four has small critical
images. A large selected image would construct a forbidden second shift. -/
theorem plane_generating_backward_shift_indices
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : GeneratingBackwardShift h p) :
    (Q Rg (p.walk.getVert (p.walk.length-2))).relIndex (Z Rg q.start) = 2 ∧
      (Q Rg q.start).relIndex (Z Rg (p.walk.getVert (p.walk.length-2))) = 2 ∧
      Nat.card (⁅Z Rg q.start,Z Rg (p.walk.getVert (p.walk.length-2))⁆ :
        Subgroup (FreeAmalgam Rg)) = 2 := by
  have hs : (Q Rg (p.walk.getVert (p.walk.length-2))).relIndex (Z Rg q.start) < 4 := by
    by_contra! hlarge
    obtain ⟨r⟩ := plane_large_generating_backward_shift h e hz hk u hR q.path hlarge
    exact plane_two_generating_backward_shifts_false h e hz hk hb u hR p q r
  have hi := small_critical_indices h e hz hk q.path hs
  exact ⟨hi.1,hi.2,small_critical_commutator_card h e hz hk q.path hs⟩

include h e hz hk in
/-- Every large critical image above distance four produces an actual
small generating backward shift, retaining its original transporter. -/
theorem plane_large_backward_small
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg a)) :
    ∃ q : GeneratingBackwardShift h p,
      (Q Rg (p.walk.getVert (p.walk.length-2))).relIndex (Z Rg q.start) = 2 ∧
      (Q Rg q.start).relIndex (Z Rg (p.walk.getVert (p.walk.length-2))) = 2 ∧
      Nat.card (⁅Z Rg q.start,Z Rg (p.walk.getVert (p.walk.length-2))⁆ :
        Subgroup (FreeAmalgam Rg)) = 2 := by
  obtain ⟨q⟩ := plane_large_generating_backward_shift h e hz hk u hR p hlarge
  exact ⟨q,plane_generating_backward_shift_indices h e hz hk hb u hR p q⟩

include h e hz hk in
/-- Every critical path above distance four is already small or reaches a
small critical pair in one actual generating backward shift. -/
theorem plane_small_critical_reachable
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    (Q Rg z).relIndex (Z Rg a) = 2 ∨
    ∃ q : GeneratingBackwardShift h p,
      (Q Rg (p.walk.getVert (p.walk.length-2))).relIndex (Z Rg q.start) = 2 ∧
      (Q Rg q.start).relIndex (Z Rg (p.walk.getVert (p.walk.length-2))) = 2 ∧
      Nat.card (⁅Z Rg q.start,Z Rg (p.walk.getVert (p.walk.length-2))⁆ :
        Subgroup (FreeAmalgam Rg)) = 2 := by
  by_cases hs : (Q Rg z).relIndex (Z Rg a) < 4
  · exact Or.inl (small_critical_indices h e hz hk p hs).1
  · exact Or.inr (plane_large_backward_small h e hz hk hb u hR p (by omega))

include h e hz hk in
/-- A small critical pair exists at every original component vertex above
distance four, with both indices two and its full noncentral line retained. -/
theorem plane_small_critical_at
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (a : Vertex Rg) (ha : color Rg a = false) :
    ∃ z, ∃ _p : CriticalPath Rg (sourceGeometry h) a z,
      (Q Rg z).relIndex (Z Rg a) = 2 ∧
      (Q Rg a).relIndex (Z Rg z) = 2 ∧
      Nat.card (⁅Z Rg a,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      (⁅Z Rg a,Z Rg z⁆ ⊓
        centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) = ⊥) := by
  have hex : ∃ c w, ∃ _p : CriticalPath Rg (sourceGeometry h) c w,
      (Q Rg w).relIndex (Z Rg c) = 2 := by
    obtain ⟨w,hw⟩ := criticalPair_exists Rg a ((sourceGeometry h).exists_critical a ha)
    let p : CriticalPath Rg (sourceGeometry h) a w := CriticalPath.ofPair ha hw
    rcases plane_small_critical_reachable h e hz hk hb u hR p with hp | ⟨q,hq,_⟩
    · exact ⟨_,_,p,hp⟩
    · exact ⟨_,_,q.path,hq⟩
  obtain ⟨c,w,p,hp⟩ := hex
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  obtain ⟨k,hkvert⟩ := exists_mVertex_of_color Rg ha
  let x := g⁻¹*k
  have hxa : act Rg x c = a := by
    rw [hg,hkvert,act_mVertex]
    dsimp only [x]
    rw [mul_inv_cancel_left]
  have hsmall : (Q Rg (act Rg x w)).relIndex (Z Rg (act Rg x c)) = 2 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hp
  have hpath : ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg x c) (act Rg x w),
      (Q Rg (act Rg x w)).relIndex (Z Rg (act Rg x c)) = 2 := ⟨p.act x,hsmall⟩
  rw [hxa] at hpath
  obtain ⟨q,hq⟩ := hpath
  have hlt : (Q Rg (act Rg x w)).relIndex (Z Rg a) < 4 := by rw [hq]; decide
  exact ⟨_,q,hq,(small_critical_indices h e hz hk q hlt).2,
    small_critical_commutator_card h e hz hk q hlt,
    small_critical_commutator_inf_centralizer h e hz hk q hlt⟩

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
