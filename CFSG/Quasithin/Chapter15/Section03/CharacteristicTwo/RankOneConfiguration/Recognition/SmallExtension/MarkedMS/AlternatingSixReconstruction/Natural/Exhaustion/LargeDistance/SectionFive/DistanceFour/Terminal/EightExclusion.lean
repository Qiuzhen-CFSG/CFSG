module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightUnequalSecondBackward
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightEqualSecondBackward

/-!
# Excluding the nonelementary order-eight image at distance four

Start with the selected strict critical path and take one backward step.
At its first edge, a stabilizer element carries the old start to the selected
start. Transporting the existing strict slice through this element gives a
concrete strict neighbor for the second step and preserves the mover comparison.
The unequal comparison closes by future-line normalization; the equal comparison
closes by the compatible paired selector and the common seed intersection.

The argument retains the literal characteristic replacement, both moving covers,
and every central attachment. Source: MS93 (5.12)(1), printed pp.924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

omit [Finite G] in
private theorem mover_act (g : FreeAmalgam d.radical) (a t : Vertex d.radical) :
    EightEdgeComparison.edgeMover (d := d) (act d.radical g a) (act d.radical g t) =
      (EightEdgeComparison.edgeMover (d := d) a t).map (MulAut.conj g⁻¹).toMonoidHom := by
  dsimp only [EightEdgeComparison.edgeMover]
  rw [SmallMover.join_map _ (MulAut.conj g⁻¹).injective,U_act,Q_act,Q_act]

omit [Finite G] in
private theorem mover_act_eq_iff (g : FreeAmalgam d.radical) (a c t : Vertex d.radical) :
    EightEdgeComparison.edgeMover (d := d) (act d.radical g a) (act d.radical g t) =
        EightEdgeComparison.edgeMover (d := d) (act d.radical g c) (act d.radical g t) ↔
      EightEdgeComparison.edgeMover (d := d) a t = EightEdgeComparison.edgeMover (d := d) c t := by
  rw [mover_act,mover_act]
  exact (Subgroup.map_injective (MulAut.conj g⁻¹).injective).eq_iff

private theorem strict_neighbor_by_transport
    (hb : replacementDistance h d = 4) {a c t : Vertex d.radical}
    (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    ∃ delta, Adjacent d.radical delta t ∧
      2 < (B d.radical c ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical delta) ∧
      (EightEdgeComparison.edgeMover (d := d) delta t = EightEdgeComparison.edgeMover (d := d) c t ↔
        EightEdgeComparison.edgeMover (d := d) c t = EightEdgeComparison.edgeMover (d := d) a t) := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨j,hj,hja⟩ := stabilizer_transitive_neighbors d.radical t
    (adjacent_symm d.radical hat) (adjacent_symm d.radical hct)
  have hjt : act d.radical j t = t := hj
  refine ⟨act d.radical j c,?_,?_,?_⟩
  · simpa only [hjt] using (adjacent_act_iff d.radical j _ _).mpr hct
  · have hi : 2 < (B d.radical (act d.radical j a)
        ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (act d.radical j c)) := by
      rw [Escape.PairingControl.FirstPairing.B_act hb2 j a ha,U_act,
        relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
      exact hstrict
    simpa only [hja] using hi
  · simpa only [hja,hjt] using mover_act_eq_iff (d := d) j c a t

include e hz hn in
private theorem backward_shift_at
    (hne : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {a z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical a t ∧
      ∃ g ∈ stabilizer d.radical a,
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical a ∧
        2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g delta) (p.walk.getVert 2),
          q.walk.getVert 1 = t ∧ q.walk.getVert 2 = a ∧
          q.walk.getVert 3 = p.walk.getVert 1 := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨j,hja⟩ : ∃ j : FreeAmalgam d.radical, act d.radical j a = alpha d.radical := by
    obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
    refine ⟨j⁻¹,?_⟩
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base := EightInitialSelection.backward_shift_knownSimple
    (e := e) (hz := hz) (hn := hn) (z := act d.radical j z)
    (delta := act d.radical j delta) hne hcard hb
  rw [←hja] at base
  have hi : 2 < (B d.radical (act d.radical j a)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (act d.radical j delta)) := by
    rw [Escape.PairingControl.FirstPairing.B_act hb2 j a p.start_color,U_act,
      relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hstrict
  obtain ⟨t,hat,g,hg,hgt,hct,hgen,hstrict',q,hq,hover⟩ :=
    base (p.act j)
      (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb (p.act j))
      (by simpa only [CriticalPath.act,actWalk_getVert] using
        (adjacent_act_iff d.radical j _ _).mpr hdelta) hi
  have hcancel (v : Vertex d.radical) : act d.radical j⁻¹ (act d.radical j v) = v := by
    rw [←act_mul,mul_inv_cancel,act_one]
  let y := j*g*j⁻¹
  have hact (v : Vertex d.radical) :
      act d.radical j⁻¹ (act d.radical g (act d.radical j v)) = act d.radical y v := by
    simp only [←act_mul,y,mul_assoc]
  have hy : y ∈ stabilizer d.radical a := by
    change act d.radical y a = a
    rw [←hact,show act d.radical g (act d.radical j a) = act d.radical j a from hg,hcancel]
  refine ⟨act d.radical j⁻¹ t,?_,y,hy,?_,?_,?_,?_,?_⟩
  · simpa only [hcancel] using (adjacent_act_iff d.radical j⁻¹ _ _).mpr hat
  · rw [←hact]
    simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act d.radical j⁻¹) hgt
  · simpa only [hact] using (adjacent_act_iff d.radical j⁻¹ _ _).mpr hct
  · have hh := congrArg (Subgroup.map (MulAut.conj (j⁻¹)⁻¹).toMonoidHom) hgen
    rwa [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hcancel,hcancel] at hh
  · have hB : (B d.radical a ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj y⁻¹).toMonoidHom = B d.radical a ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        hb2 a p.start_color ((stabilizer d.radical a).inv_mem hy))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hstrict
  · have hl2 : (p.act j).walk.length-2 = 2 := by
      simp only [CriticalPath.act,actWalk_length,hl]
    have hq2 : q.walk.getVert 2 = act d.radical j a := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
    have hq3 : q.walk.getVert 3 = act d.radical j (p.walk.getVert 1) := by
      simpa only [CriticalPath.act,actWalk_getVert] using hover 1 (by omega)
    have hend : act d.radical j⁻¹ ((p.act j).walk.getVert ((p.act j).walk.length-2)) =
        p.walk.getVert 2 := by
      rw [hl2]
      simp only [CriticalPath.act,actWalk_getVert,hcancel]
    have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical j⁻¹ (act d.radical g (act d.radical j delta)))
        (act d.radical j⁻¹ ((p.act j).walk.getVert ((p.act j).walk.length-2))),
        w.walk.getVert 1 = act d.radical j⁻¹ t ∧
        w.walk.getVert 2 = a ∧ w.walk.getVert 3 = p.walk.getVert 1 := by
      refine ⟨q.act j⁻¹,?_,?_,?_⟩
      · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act d.radical j⁻¹) hq
      · simpa only [CriticalPath.act,actWalk_getVert,hcancel] using congrArg (act d.radical j⁻¹) hq2
      · simpa only [CriticalPath.act,actWalk_getVert,hcancel] using congrArg (act d.radical j⁻¹) hq3
    rwa [hend,hact] at hex

include e hz hn in
private theorem unequal_first_false
    (hne₀ : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z = stabilizer d.radical a)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgc : act d.radical g (p.walk.getVert 2) = c)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c))
    (hne : EightEdgeComparison.edgeMover (d := d) c (q.walk.getVert 1) ≠
      EightEdgeComparison.edgeMover (d := d) a (q.walk.getVert 1)) : False := by
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb
  have hct : Adjacent d.radical c (q.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a (q.walk.getVert 1) := by
    simpa only [hq2] using adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨delta,hdelta,hi,hcmp⟩ := strict_neighbor_by_transport hb p.start_color hat hct hstrict
  have select := backward_shift_at hne₀ hcard hb q hdelta hi
  rw [hq2] at select
  obtain ⟨u,_,k,hk,hku,_,hrgen,hrstrict,r,hr1,hr2,_⟩ := select
  have hneq : EightEdgeComparison.edgeMover (d := d) (act d.radical k delta) u ≠
      EightEdgeComparison.edgeMover (d := d) c u := by
    intro he
    have hkc : act d.radical k c = c := hk
    have he' := mover_act_eq_iff (d := d) k delta c (q.walk.getVert 1)
    rw [hku,hkc] at he'
    exact hne (hcmp.mp (he'.mp he))
  exact eight_unequal_second_backward_strict_false_knownSimple hne₀ hcard hb p q hq2
    hgen g hg hgc r hr2 (hr1 ▸ hneq) (hr1 ▸ hrgen) hrstrict

include e hz hn in
/-- The nonelementary radical image of order eight cannot have replacement
distance four. All path-selection and terminal premises are discharged. -/
theorem eight_distance_four_false_knownSimple
    (hne : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4) : False := by
  obtain ⟨z,p,_,hi⟩ := EightInitialSelection.initial_selection_knownSimple hne hcard hb
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hmid : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,g,hg,_,hct,hgen,hstrict,q,hq1,hq2,_⟩ :=
    backward_shift_at hne hcard hb p hmid hi
  have hgen' : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z =
      stabilizer d.radical (alpha d.radical) := hq1 ▸ hgen
  by_cases heq : EightEdgeComparison.edgeMover (d := d) (act d.radical g (p.walk.getVert 2))
      (q.walk.getVert 1) = EightEdgeComparison.edgeMover (d := d) (alpha d.radical) (q.walk.getVert 1)
  · obtain ⟨delta,hdelta,hstrict2,hcmp⟩ := strict_neighbor_by_transport hb p.start_color
      (show Adjacent d.radical (alpha d.radical) (q.walk.getVert 1) from hq1 ▸ hat)
      (show Adjacent d.radical (act d.radical g (p.walk.getVert 2)) (q.walk.getVert 1) from hq1 ▸ hct)
      hstrict
    exact eight_equal_second_backward_strict_false_knownSimple hne hcard hb p q hq2
      hgen' g hg rfl hstrict heq hdelta (hcmp.mpr heq) hstrict2
  · exact unequal_first_false hne hcard hb p q hq2 hgen' g hg rfl hstrict heq

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
