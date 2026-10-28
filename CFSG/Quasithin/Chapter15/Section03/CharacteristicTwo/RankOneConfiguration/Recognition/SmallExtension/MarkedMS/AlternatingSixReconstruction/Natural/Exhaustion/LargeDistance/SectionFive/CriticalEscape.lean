module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.PredecessorSlice

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Extensions

/-!
# Universal critical escape and forward slice choices

The full-point radius-escape theorem applies to every predecessor on a
critical geodesic. Assemble a geodesic through a prescribed predecessor and
transport it to the base vertex. This supplies the exact universal escape
premise of MS93 2.2(v). Reverse critical nonnormality then forces the original
second moving cover outside the starting Baumann subgroup, giving forward
slice index at least two without an eligibility assumption.

Apply universal escape to the reversed path to extend the original endpoint
by two edges. The new critical walk starts at the old second vertex, retains
every shared vertex, and has the old endpoint as its second predecessor.
For a small forward slice and small original critical image, eligibility
makes the existing forward commutator a noncentral line of order two. One
component conjugator gives both the generating centralizer and movement by
the newly constructed endpoint seed, as required for the second starred
choice in the proof of (5.9).

The applications use the actual characteristic replacement and its canonical
symmetric quotient. The order-16 and order-32 covers, including the latter's
central line, are retained. Full point-core image is an explicit branch;
the strict index bound above two, other radical images, exact-four exclusion,
intermediate R4/R6 noncentrality and both terminal contradictions remain.
No natural subgroup replaces the original quotient or its transfer premises.

Source: Meierfrankenfeld--Stellmacher (1993), (2.2)(v), pp.856--857,
(5.8), pp.919--920, and the second starred choice of (5.9), p.920.
The universal transport and reverse-nonnormality arguments adapt
SymplecticSetup.BackwardEscape and ShiftedSeedChoiceAll to both central
covers, using the proved predecessor-slice and residual-shift calculation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include h in
private theorem core_residual_edge_generation {a t : Vertex d.radical}
    (ha : color d.radical a = false) (hat : Adjacent d.radical a t) :
    Ltilde d.radical a ⊔ Q d.radical t = stabilizer d.radical a := by
  have hsup : replacementComponent d ⊔ d.radical = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨k,hk,r,hr,rfl⟩ := replacement_product h d g
    exact mul_mem (mem_sup_left hk) (mem_sup_right hr)
  have hbase : Ltilde d.radical (alpha d.radical) ⊔ Q d.radical (beta d.radical) =
      stabilizer d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d,Q_beta,←Subgroup.map_sup,hsup]
    exact (MonoidHom.range_eq_map (embedM d.radical)).symm.trans (stabilizer_m_base d.radical).symm
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act] at he
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using he
  · rw [hg.1] at ha
    cases ha

private theorem normalizes_join_of_displacement {G : Type*} [Group G]
    (N H K : Subgroup G) (hn : K≤normalizer (N:Set G))
    (hcomm : ⁅K,H⁆≤N) : K≤normalizer ((N⊔H:Subgroup G):Set G) := by
  apply le_normalizer_iff.mpr
  intro k hk x hx
  have hm : (N⊔H).map (MulAut.conj k).toMonoidHom≤N⊔H := by
    rw [Subgroup.map_sup]
    refine sup_le ((mem_normalizer_iff_map_conj_eq.mp (hn hk)).le.trans le_sup_left) ?_
    rintro _ ⟨y,hy,rfl⟩
    have hh := (N⊔H).mul_mem
      (mem_sup_left (hcomm (commutator_mem_commutator hk hy))) (mem_sup_right hy)
    simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
  exact hm (mem_map_of_mem (MulAut.conj k).toMonoidHom hx)

include s in
private theorem full_point_escape_base
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (hcrit : CriticalPair d.radical (alpha d.radical) a'
      ((replacementGeometry h d).exists_critical _ rfl))
    (c : Vertex d.radical) (hce : (cosetGraph d.radical).dist c a' = 2)
    (hpath : (cosetGraph d.radical).dist (alpha d.radical) c + 2 =
      (cosetGraph d.radical).dist (alpha d.radical) a') :
    ¬ V d.radical (alpha d.radical) ≤ Q d.radical c := by
  obtain ⟨w,hw⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist (alpha d.radical) c
  obtain ⟨v,hv⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist c a'
  let p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a' :=
    ⟨rfl,w.append v,by rw [SimpleGraph.Walk.length_append,hw,hv,hce,hpath],hcrit⟩
  have heq : p.walk.getVert (p.walk.length-2) = c := by
    change (w.append v).getVert ((w.append v).length-2) = c
    rw [SimpleGraph.Walk.length_append,hv,hce,Nat.add_sub_cancel]
    simp only [SimpleGraph.Walk.getVert_append,lt_self_iff_false,ite_false,
      Nat.sub_self,SimpleGraph.Walk.getVert_zero]
  obtain ⟨t,hat,hgen⟩ := full_point_generating_neighbor s hc u hfull p
  simpa only [heq] using radius_not_le_predecessor_of_generating_edge s hc hb u hfull.le p hat hgen

include s in
/-- The full-point replacement satisfies the universal radius-escape premise
of MS93 2.2(v). Transport preserves the original graph and both covers. -/
theorem full_point_criticalEscape
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom) :
    Factorization.CriticalEscape d.radical (replacementGeometry h d) := by
  intro a ha a' hcrit c hce hpath
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
  have hbase : act d.radical g⁻¹ (mVertex d.radical g) = alpha d.radical := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have ha' : color d.radical (act d.radical g⁻¹ (mVertex d.radical g)) = false := by
    rw [hbase]
    rfl
  have hcrit' := (criticalPair_act_iff d.radical g⁻¹ (mVertex d.radical g) a'
    ((replacementGeometry h d).exists_critical _ ha)
    ((replacementGeometry h d).exists_critical _ ha')).mpr hcrit
  have hcritbase : CriticalPair d.radical (alpha d.radical) (act d.radical g⁻¹ a')
      ((replacementGeometry h d).exists_critical _ rfl) := by
    simpa only [hbase] using hcrit'
  have hce' : (cosetGraph d.radical).dist (act d.radical g⁻¹ c) (act d.radical g⁻¹ a') = 2 := by
    rw [dist_act]
    exact hce
  have hpath' : (cosetGraph d.radical).dist (alpha d.radical) (act d.radical g⁻¹ c) + 2 =
      (cosetGraph d.radical).dist (alpha d.radical) (act d.radical g⁻¹ a') := by
    rw [←hbase,dist_act,dist_act]
    exact hpath
  have hn := full_point_escape_base s hc hb u hfull hcritbase (act d.radical g⁻¹ c) hce' hpath'
  intro hV
  apply hn
  have hh := map_mono (f := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom) hV
  rw [←V_act,←Q_act,hbase] at hh
  exact hh

include s in
/-- Universal escape makes the forward moving cover eligible on every
critical path. Reverse nonnormality is applied in the actual stabilizer. -/
theorem critical_forward_not_le_slice_of_escape
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (hesc : Factorization.CriticalEscape d.radical (replacementGeometry h d))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ¬ U d.radical (p.walk.getVert 2) ≤ B d.radical a ((replacementGeometry h d).Z_normal _) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hpos : 0 < criticalDistance d.radical a ((replacementGeometry h d).exists_critical a p.start_color) := by
    rw [(replacementGeometry h d).distance_constant a p.start_color]
    exact replacementDistance_pos h d
  have hac : (cosetGraph d.radical).dist a c = 2 := p.dist_start (by omega)
  have hpath : (cosetGraph d.radical).dist c a' + 2 = (cosetGraph d.radical).dist a a' := by
    rw [p.dist_end,←p.shortest]
    omega
  have hn := (critical_nonnormal_reverse d.radical (replacementGeometry h d)
    (edgeCentralizerCondition s hc) hesc a p.start_color hpos p.critical c hac hpath).2
  intro hU
  have hZB : Z d.radical c ≤ B d.radical a ((replacementGeometry h d).Z_normal _) := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d hcol hct]
    exact sup_le hU ((adjacent_Z_le d.radical p.start_color hat).trans
      (Escape.EdgeTransfer.Z_le_B hb a p.start_color))
  have hZX : Z d.radical a ≤ X d.radical a :=
    Z_le_X_of_positive d.radical a p.start_color
      ((replacementGeometry h d).exists_critical a p.start_color) hpos
  apply hn
  apply normal_subgroupOf_of_le_normalizer
  rw [←core_residual_edge_generation (h := h) p.start_color hat,
    sup_comm (Z d.radical c) (X d.radical a)]
  apply sup_le
  · apply normalizes_join_of_displacement
    · exact (Ltilde_le_stabilizer a).trans (X_normalized d.radical a)
    · apply commutator_le.mpr
      intro l hl z hz
      exact hZX (((mem_B_iff d.radical a _
        ((replacementGeometry h d).V_local a p.start_color (by
          rw [(replacementGeometry h d).distance_constant a p.start_color]; exact hb)) z).mp (hZB hz)).2 l hl)
  · have htG : Q d.radical t ≤ stabilizer d.radical a :=
      fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
    have htC : Q d.radical t ≤ stabilizer d.radical c :=
      fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
    exact (le_inf (htG.trans (X_normalized d.radical a))
      (htC.trans (Z_normalized d.radical c))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

include s in
/-- The forward index in source (5.8), without a separately assumed eligible
slice. This is the lower bound two; (5.9) requires strict inequality. -/
theorem critical_forward_slice_index_two_le_of_escape
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (hesc : Factorization.CriticalEscape d.radical (replacementGeometry h d))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  let := finite_Z d.radical (p.walk.getVert 2)
  let : Finite (U d.radical (p.walk.getVert 2)) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical _)) (inclusion_injective _)
  have hpos : 0 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hne : (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≠ 1 :=
    fun he => critical_forward_not_le_slice_of_escape s hc hb hesc p (relIndex_eq_one.mp he)
  omega

include s in
/-- Extend the same critical walk forward by two edges and remove its first
two edges. Every shared vertex is retained, including the old endpoint as
the new predecessor. The escape premise supplies the new endpoint. -/
theorem critical_forward_extension_of_escape
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (hesc : Factorization.CriticalEscape d.radical (replacementGeometry h d))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) z,
      (cosetGraph d.radical).dist a' z = 2 ∧
      (∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) ∧
      q.walk.getVert (q.walk.length-2) = a' := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hca : (cosetGraph d.radical).dist (p.walk.getVert 2) a = 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)]
  have hec : (cosetGraph d.radical).dist a' (p.walk.getVert 2) + 2 =
      (replacementGeometry h d).b d.radical := by
    rw [SimpleGraph.dist_comm,p.dist_end,p.length_eq_b]
    change replacementDistance h d - 2 + 2 = replacementDistance h d
    omega
  have hpath : (cosetGraph d.radical).dist a' (p.walk.getVert 2) + 2 =
      (cosetGraph d.radical).dist a' a := by
    rw [hec,SimpleGraph.dist_comm,←p.shortest,p.length_eq_b]
  have hescape := hesc a' p.end_color a (critical_reverse_pair s hc p)
    (p.walk.getVert 2) hca hpath
  obtain ⟨z,hz,hze,hcrit⟩ := exists_critical_shift d.radical p.end_color hec hescape
  have hrev : CriticalPair d.radical (p.walk.getVert 2) z
      ((replacementGeometry h d).exists_critical _ hcol) := by
    apply critical_reverse d.radical (replacementGeometry h d) (edgeCentralizerCondition s hc)
      z hz _ _ hcol hcrit
    rw [(replacementGeometry h d).distance_constant z hz]
    exact replacementDistance_pos h d
  obtain ⟨v,hv⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist a' z
  have hvlen : v.length = 2 := hv.trans (SimpleGraph.dist_comm.trans hze)
  let w := (p.walk.drop 2).append v
  have hwlen : w.length = p.walk.length := by
    simp only [w,SimpleGraph.Walk.length_append,SimpleGraph.Walk.drop_length,hvlen]
    omega
  let q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) z :=
    ⟨hcol,w,by rw [hwlen,p.length_eq_b,hrev.1,
      (replacementGeometry h d).distance_constant _ hcol]; rfl,hrev⟩
  have hover (i : ℕ) (hi : i ≤ p.walk.length-2) :
      q.walk.getVert i = p.walk.getVert (i+2) := by
    change w.getVert i = _
    rw [SimpleGraph.Walk.getVert_append',SimpleGraph.Walk.drop_length,if_pos hi,
      SimpleGraph.Walk.drop_getVert,Nat.add_comm 2 i]
  refine ⟨z,q,by simpa only [SimpleGraph.dist_comm] using hze,hover,?_⟩
  change w.getVert (w.length-2) = a'
  rw [hwlen]
  change q.walk.getVert (p.walk.length-2) = a'
  rw [hover _ le_rfl,show p.walk.length-2+2 = p.walk.length by omega,p.walk.getVert_length]

/-- The original full-point replacement now supplies both forward slice
indices and the literal shifted critical path, on either central cover.
The new path shares every vertex from the old second vertex to its endpoint. -/
theorem full_point_forward_path_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) ∧
      2 ≤ (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical a) ∧
      ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) z,
        (cosetGraph d.radical).dist a' z = 2 ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) ∧
        q.walk.getVert (q.walk.length-2) = a' := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hesc := full_point_criticalEscape s hc hb u hfull'
  exact ⟨critical_forward_slice_index_two_le_of_escape s hc hb hesc p,
    critical_start_slice_index_two_le s hc hb p,
    critical_forward_extension_of_escape s hc hb hesc p⟩

/-- The full-point source supplies eligibility for the small forward-slice
line. Only the numerical upper slice and small critical-image premises remain;
the line is central at the start and noncentral at the original second vertex. -/
theorem full_point_small_forward_line_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical (p.walk.getVert 2),T⁆
    (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) = 2 ∧
      Nat.card H = 2 ∧ H ≤ Z d.radical (p.walk.getVert 1) ∧
      H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
      ¬ H ≤ centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  exact small_forward_slice_line_knownSimple (e := e) (hz := hz) (hn := hn) hb p hslice hsmall
    (critical_forward_not_le_slice_of_escape s hc hb (full_point_criticalEscape s hc hb u hfull') p)

/-- The small full-point forward slice supplies the shifted endpoint and
one component conjugator for both generation and line movement, as used in
the second starred choice of (5.9). The same shifted walk retains all shared
vertices; no endpoint, nonzero-line, or eligibility premise is added. -/
theorem full_point_forward_shifted_line_choice_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    let c := p.walk.getVert 2
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical c,T⁆
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) c z,
      (cosetGraph d.radical).dist a' z = 2 ∧
      (∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) ∧
      q.walk.getVert (q.walk.length-2) = a' ∧
      ∃ g ∈ Ltilde d.radical c,
        (stabilizer d.radical c ⊓ centralizer
          (H.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊔
            Z d.radical z = stabilizer d.radical c ∧
        ¬ H.map (MulAut.conj g).toMonoidHom ≤ centralizer
          (Z d.radical z : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T⁆
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hTG : T ≤ stabilizer d.radical c :=
    (inf_le_left.trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hHU : H ≤ U d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized c))
  have hline := full_point_small_forward_line_knownSimple hb u hfull p hslice hsmall
  obtain ⟨_,_,z,q,haz,hover,hpre⟩ := full_point_forward_path_knownSimple hb u hfull p
  refine ⟨z,q,haz,hover,hpre,?_⟩
  exact exists_cover_line_generator s hc q H hHU hline.2.1 hline.2.2.2.2

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

