module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FullSeed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.StrictSlices

/-!
# Reciprocal selection at distance four for every radical image

An endpoint commutator estimate makes a selected orbit span nonabelian as
soon as its own forward seed escapes the Baumann slice. This local criterion
uses no universal critical-escape hypothesis.

Now suppose a nonabelian selected span has a small forward slice. Its
noncommuting conjugate seeds supply a reciprocal critical path through the
same first edge and original base. The transported small slice identifies
the whole reverse kernel inside the two inner seeds, so the common two-core
kernel has the exact critical endpoint commutator. Source (2.2)(iv), applied
to the original path, supplies eligibility on this reciprocal path. The local
criterion therefore makes the reciprocal span nonabelian. If its forward
slice were also small, the existing full-seed terminal theorem would give a
contradiction. Thus the reciprocal slice is large.

The final application constructs a nonabelian large-slice critical path at
the original base from any nonabelian selected path. The original graph,
full seeds, both moving covers and all radical images are retained. Initial
nonabelian selection, the large-slice exclusion and the whole residual-core
upper estimates remain open; this does not assert DistanceFourInput.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (2.2)(iv), printed pp.856--857, and the reciprocal selection and
Baumann-slice arguments in (5.12), printed pp.924--927. Uses the literal
midpoint-kernel and full-seed terminal calculations of this development.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- The literal endpoint estimate and eligibility of this one seed suffice
for nonabelianness. No universal critical-escape hypothesis is needed. -/
theorem selected_span_nonabelian_of_eligible_endpoint
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (helig : ¬ U d.radical (p.walk.getVert 2) ≤
      B d.radical a ((replacementGeometry h d).Z_normal _))
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) a ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical a) :
    ⁅localZSpan d.radical (p.walk.getVert 2) a,
      localZSpan d.radical (p.walk.getVert 2) a⁆ ≠ ⊥ := by
  let c := p.walk.getVert 2
  let P := localZSpan d.radical c a
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hac : (cosetGraph d.radical).dist a c = 2 := p.dist_start (by omega)
  have hPV : P ≤ V d.radical a := localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm,hac])
  have hPQ : P ≤ Q d.radical a := hPV.trans (V_le_Q d.radical p.start_color hb)
  have hPG : P ≤ stabilizer d.radical c := hPQ.trans
    (Q_le_stabilizer_of_dist_two d.radical a c p.start_color hac)
  intro hzero
  have hPC : P ≤ Q d.radical c := by
    rw [←C_eq_Q s hc c hcol]
    exact le_inf hPG ((commutator_eq_bot_iff_le_centralizer.mp hzero).trans
      (centralizer_le (Z_le_localZSpan d.radical c a)))
  have hPB := normalized_radius_le_slice_of_actor_at s hb p.start_color P (Z d.radical a')
    hPV (localZSpan_normalized d.radical c a)
    (critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
      (by rw [(replacementGeometry h d).distance_constant _ p.start_color]
          exact replacementDistance_pos h d) p.critical)
    (critical_reverse_pair s hc p).2
    (by
      have hh : ⁅P ⊓ Q d.radical c,Z d.radical a'⁆ ≤ Z d.radical a := hcomm
      rwa [inf_eq_left.mpr hPC] at hh)
  exact helig ((DistanceEight.U_le_Z d.radical c).trans
    ((Z_le_localZSpan d.radical c a).trans hPB))

include e hz hn in
private theorem terminal_at
    (hb : replacementDistance h d = 4) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hnon : ⁅localZSpan d.radical (p.walk.getVert 2) a,
      localZSpan d.radical (p.walk.getVert 2) a⁆ ≠ ⊥)
    (hslice : (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical (p.walk.getVert 2))
    (he : act d.radical x a = a')
    (hpre : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hrestore (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have base := selected_terminal_false_of_full_seed_slices_knownSimple
    (e := e) (hz := hz) (hn := hn) hb (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  have hn' : ⁅localZSpan d.radical ((p.act g⁻¹).walk.getVert 2) (act d.radical g⁻¹ a),
      localZSpan d.radical ((p.act g⁻¹).walk.getVert 2) (act d.radical g⁻¹ a)⁆ ≠ ⊥ := by
    change ⁅localZSpan d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2) _,
      localZSpan d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2) _⁆ ≠ ⊥
    rw [actWalk_getVert,LocalCommutator.CriticalCase.localZSpan_act,←map_commutator]
    exact fun hh => hnon ((map_eq_bot_iff_of_injective _ (MulAut.conj _).injective).mp hh)
  have hs' : (B d.radical (act d.radical g⁻¹ a) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical ((p.act g⁻¹).walk.getVert 2)) ≤ 2 := by
    change (B d.radical _ _).relIndex (U d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2)) ≤ 2
    rw [actWalk_getVert,Escape.PairingControl.FirstPairing.B_act hb2 _ _ p.start_color,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hslice
  let k := g*x*g⁻¹
  have hk : k ∈ stabilizer d.radical ((p.act g⁻¹).walk.getVert 2) := by
    change k ∈ stabilizer d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2)
    rw [actWalk_getVert,stabilizer_act]
    refine ⟨x,hx,?_⟩
    change (g⁻¹)⁻¹*x*((g⁻¹)⁻¹)⁻¹ = k
    simp only [inv_inv,k]
  have hke : act d.radical k (act d.radical g⁻¹ a) = act d.radical g⁻¹ a' := by
    dsimp only [k]
    rw [act_mul,act_mul,hrestore,he]
  have hp' : (B d.radical ((p.act g⁻¹).walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical g⁻¹ a')) ≤ 2 := by
    change (B d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (act d.radical g⁻¹ a')) ≤ 2
    rw [actWalk_getVert,Escape.PairingControl.FirstPairing.B_act hb2 _ _ hcol,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hpre
  exact base (p.act g⁻¹) hn' hs' k hk hke hp'

include e hz hn in
/-- A nonabelian small-slice span forces a nonabelian reciprocal span and a
large reciprocal slice. This uses the same two vertices and all radical images. -/
theorem small_slice_reciprocal_large_knownSimple
    (hb : replacementDistance h d = 4) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnon : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    ⁅localZSpan d.radical (alpha d.radical) (p.walk.getVert 2),
      localZSpan d.radical (alpha d.radical) (p.walk.getVert 2)⁆ ≠ ⊥ ∧
      2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (alpha d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨_,x,hx,q,hq1,hq2,hq3⟩ := selected_span_conjugate_critical_path (h := h) hb2 p hnon
  have hBm : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      (geometry := replacementGeometry h d) hb2 (alpha d.radical) rfl
      ((stabilizer d.radical (alpha d.radical)).inv_mem hx))
  have hi : (B d.radical (q.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical x (p.walk.getVert 2))) ≤ 2 := by
    rw [hq2,U_act,←hBm,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hslice
  have hcomm := (midpoint_common_kernel_endpoint_commutator s hc hb q x (hq2.symm ▸ hx) rfl hi).2
  have hqP : localZSpan d.radical (q.walk.getVert 2) (p.walk.getVert 2) ≤
      Q d.radical (p.walk.getVert 2) :=
    (localZSpan_le_V d.radical (by
      rw [SimpleGraph.dist_comm,q.dist_start (by have hl := q.length_eq_b.trans hb; omega)])).trans
      (V_le_Q d.radical q.start_color hb2)
  have hnq := selected_span_nonabelian_of_eligible_endpoint s hc hb2 q
    (by simpa only [hq2] using critical_start_not_le_second_slice s hc hb2 p)
    ((commutator_mono (inf_le_inf_right _ hqP) le_rfl).trans
      (hcomm.le.trans (((critical_Z_commutator_le_moving (h := h) q).trans inf_le_left).trans
        (DistanceEight.U_le_Z d.radical _))))
  refine ⟨by simpa only [hq2] using hnq,?_⟩
  by_contra! hopposite
  exact terminal_at (e := e) (hz := hz) (hn := hn) hb q hnq
    (by simpa only [hq2] using hopposite) x (hq2.symm ▸ hx) rfl hi

include e hz hn in
/-- Any nonabelian selected span at distance four supplies a nonabelian
large-slice critical path at the original base. In the small-slice case the
path is the reciprocal conjugate path, transported by one graph action. -/
theorem exists_nonabelian_large_slice_knownSimple
    (hb : replacementDistance h d = 4) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnon : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥) :
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      ⁅localZSpan d.radical (q.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (q.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (q.walk.getVert 2)) := by
  by_cases hs : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))
  · exact ⟨a',p,hnon,hs⟩
  have hb2 : 2 < replacementDistance h d := by omega
  have hrec := small_slice_reciprocal_large_knownSimple (e := e) (hz := hz) (hn := hn)
    hb p hnon (by omega)
  obtain ⟨_,x,hx,q,_,hq,_⟩ := selected_span_conjugate_critical_path (h := h) hb2 p hnon
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical q.start_color
  have hbase : act d.radical g⁻¹ (p.walk.getVert 2) = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hnq : ⁅localZSpan d.radical (q.walk.getVert 2) (p.walk.getVert 2),
      localZSpan d.radical (q.walk.getVert 2) (p.walk.getVert 2)⁆ ≠ ⊥ := by
    simpa only [hq] using hrec.1
  have hlarge : 2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (q.walk.getVert 2)) := by simpa only [hq] using hrec.2
  have hn' : ⁅localZSpan d.radical ((q.act g⁻¹).walk.getVert 2)
        (act d.radical g⁻¹ (p.walk.getVert 2)),
      localZSpan d.radical ((q.act g⁻¹).walk.getVert 2)
        (act d.radical g⁻¹ (p.walk.getVert 2))⁆ ≠ ⊥ := by
    change ⁅localZSpan d.radical ((actWalk d.radical g⁻¹ q.walk).getVert 2) _,
      localZSpan d.radical ((actWalk d.radical g⁻¹ q.walk).getVert 2) _⁆ ≠ ⊥
    rw [actWalk_getVert,LocalCommutator.CriticalCase.localZSpan_act,←map_commutator]
    exact fun hh => hnq ((map_eq_bot_iff_of_injective _ (MulAut.conj _).injective).mp hh)
  have hl' : 2 < (B d.radical (act d.radical g⁻¹ (p.walk.getVert 2))
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical ((q.act g⁻¹).walk.getVert 2)) := by
    change 2 < (B d.radical _ _).relIndex (U d.radical ((actWalk d.radical g⁻¹ q.walk).getVert 2))
    rw [actWalk_getVert,Escape.PairingControl.FirstPairing.B_act hb2 _ _ q.start_color,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge
  have hex : ∃ r : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical g⁻¹ (p.walk.getVert 2)) (act d.radical g⁻¹ (act d.radical x (p.walk.getVert 2))),
      ⁅localZSpan d.radical (r.walk.getVert 2) (act d.radical g⁻¹ (p.walk.getVert 2)),
        localZSpan d.radical (r.walk.getVert 2) (act d.radical g⁻¹ (p.walk.getVert 2))⁆ ≠ ⊥ ∧
        2 < (B d.radical (act d.radical g⁻¹ (p.walk.getVert 2))
          ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (r.walk.getVert 2)) :=
    ⟨q.act g⁻¹,hn',hl'⟩
  rw [hbase] at hex
  obtain ⟨r,hr⟩ := hex
  exact ⟨_,r,hr⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
