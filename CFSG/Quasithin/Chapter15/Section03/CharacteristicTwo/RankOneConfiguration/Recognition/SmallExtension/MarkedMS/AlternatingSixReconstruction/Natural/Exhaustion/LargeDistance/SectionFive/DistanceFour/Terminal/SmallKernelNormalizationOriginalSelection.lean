module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelNormalizationIntersection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightCompatibleOriginal
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalLines
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightEqual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightEqual

/-!
# Compatible backward selection at the original image-eight edge

The original-edge paired selector retains common-fixer centrality against both
paired selected movers. Strictness identifies each seed intersection with its
full mover fixer. Whichever paired backward candidate escapes the terminal
core therefore gives an actual critical path whose triple seed intersection
is central at the original vertex. The paired endpoint orientation is pulled
back using the same actor, retaining generation and the complete path overlap.

Source: MS93 (5.5)--(5.7), (5.12)(1), printed pp.916--919,924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


private theorem compatible_prepend_backward
  (hb : 2 < replacementDistance h d) {a c t v : Vertex d.radical}
  (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
  (hcol : color d.radical c = false)
    (b : CriticalPath d.radical (replacementGeometry h d) a v)
    (hbad : ¬ Z d.radical c ≤ Q d.radical (b.walk.getVert (b.walk.length-2))) :
    ∃ r : CriticalPath d.radical (replacementGeometry h d)
        c (b.walk.getVert (b.walk.length-2)),
      r.walk.getVert 1 = t ∧
      ∀ i ≤ b.walk.length-2, r.walk.getVert (i+2) = b.walk.getVert i := by
  let w : (cosetGraph d.radical).Walk c a :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  have hb2 : 2 ≤ (replacementGeometry h d).b d.radical := by
    change 2 ≤ replacementDistance h d
    omega
  let r := b.prepend_two hb2 hcol w hw hbad
  refine ⟨r,?_,fun i hi => b.prepend_two_overlap _ _ _ _ _ hi⟩
  change (b.prepend_two _ hcol w hw hbad).walk.getVert 1 = t
  rw [CriticalPath.prepend_two_walk]
  simp only [SimpleGraph.Walk.getVert_append,hw,show 1<2 from by decide,ite_true,
    w,SimpleGraph.Walk.getVert_cons_succ,SimpleGraph.Walk.getVert_zero]

include e hz hn in
theorem eight_equal_compatible_backward_base_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hgenAll : ∀ w : Vertex d.radical, color d.radical w = false →
      X d.radical w = U d.radical w ⊔
        (X d.radical w ⊓ centralizer (stabilizer d.radical w : Set (FreeAmalgam d.radical))))
    (hdelta : Adjacent d.radical delta (beta d.radical))
    (hequal : EightEdgeComparison.edgeMover (d := d) delta (beta d.radical) =
      EightEdgeComparison.edgeMover (d := d) (alpha d.radical) (beta d.radical))
    (hstrict : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical delta)) :
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      let c := act d.radical g delta
      let t := act d.radical g (beta d.radical)
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
        EightEdgeComparison.edgeMover (d := d) c t =
          EightEdgeComparison.edgeMover (d := d) (alpha d.radical) t ∧
        Z d.radical delta ⊓ Z d.radical (alpha d.radical) ⊓ Z d.radical c ≤
          centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
        2 < (B d.radical (alpha d.radical)
          ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            c (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  obtain ⟨_,_,_,g,hg,x,hxL,_,_,hat,hgen,hxpair,hleft,hright,_,hcross0,hcross1⟩ :=
    EightCompatibleOriginal.paired_generating_original_cube_knownSimple
      (e := e) (hz := hz) (hn := hn) hne hcard hb hmodel p hsmall hfirst
  let c := act d.radical g delta
  let t := act d.radical g (beta d.radical)
  have hx : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hxL
  have hct : Adjacent d.radical c t := (adjacent_act_iff d.radical g _ _).mpr hdelta
  have hga : act d.radical g (alpha d.radical) = alpha d.radical := hg
  have equalAt (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical (alpha d.radical)) :
      EightEdgeComparison.edgeMover (d := d) (act d.radical y delta) (act d.radical y (beta d.radical)) =
      EightEdgeComparison.edgeMover (d := d) (alpha d.radical) (act d.radical y (beta d.radical)) := by
    have hh := congrArg (Subgroup.map (MulAut.conj y⁻¹).toMonoidHom) hequal
    dsimp only [EightEdgeComparison.edgeMover] at hh ⊢
    rw [SmallMover.join_map _ (MulAut.conj y⁻¹).injective,
      SmallMover.join_map _ (MulAut.conj y⁻¹).injective,←U_act,←Q_act,←Q_act,
      ←U_act,←Q_act,show act d.radical y (alpha d.radical) = alpha d.radical from hy] at hh
    exact hh
  have hEq := equalAt g hg
  have strict (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical (alpha d.radical)) :
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (act d.radical y delta)) := by
    have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj y⁻¹).toMonoidHom =
        B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        (by omega : 2 < replacementDistance h d) _ rfl ((stabilizer d.radical _).inv_mem hy))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hstrict
  have tripleAt (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical (alpha d.radical))
      (hfix : (Z d.radical (alpha d.radical) ⊓ centralizer
        (EightEdgeComparison.edgeMover (d := d) (alpha d.radical) (beta d.radical) : Set (FreeAmalgam d.radical))) ⊓
        centralizer (EightEdgeComparison.edgeMover (d := d) (alpha d.radical)
          (act d.radical y (beta d.radical)) : Set (FreeAmalgam d.radical)) =
        Z d.radical (alpha d.radical) ⊓ centralizer
          (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))) :
      Z d.radical delta ⊓ Z d.radical (alpha d.radical) ⊓ Z d.radical (act d.radical y delta) ≤
        centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
    have hay : Adjacent d.radical (alpha d.radical) (act d.radical y (beta d.radical)) := by
      have he : act d.radical y (alpha d.radical) = alpha d.radical := hy
      rw [←he]
      exact (adjacent_act_iff d.radical y _ _).mpr (base_adjacent d.radical)
    exact eight_equal_compatible_triple_central_knownSimple
      (e := e) (hz := hz) (hn := hn) hne hcard hb rfl (base_adjacent d.radical) hdelta
      hay ((adjacent_act_iff d.radical y _ _).mpr hdelta) hequal (equalAt y hy)
      hgenAll hstrict (strict y hy) hfix
  have hxa : act d.radical x (alpha d.radical) = alpha d.radical := hx
  obtain ⟨q,hq⟩ : ∃ q : CriticalPath d.radical (replacementGeometry h d)
      (alpha d.radical) (act d.radical x z),
      ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) := by
    have hh : ∃ q : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical x (alpha d.radical)) (act d.radical x z),
        ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) :=
      ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
    rwa [hxa] at hh
  have hqs : (Q d.radical (act d.radical x z)).relIndex
      (Z d.radical (alpha d.radical)) < 4 := by
    conv_lhs => rhs; rw [←hxa]
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hsmall
  have hLgen : Ltilde d.radical (alpha d.radical) ≤
      EightEdgeComparison.edgeMover (d := d) c t ⊔ Z d.radical z ⊔
        Z d.radical (act d.radical x z) := by
    rw [hEq,hgen]
    exact Ltilde_le_stabilizer _
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hdelta
    have hc : color d.radical delta = false := by
      change color d.radical delta ≠ true at hh
      cases hc : color d.radical delta <;> simp_all
    change color d.radical (act d.radical g delta) = false
    rw [action_preserves_color,hc]
  by_cases hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))
  · have hqbad : ¬ Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
      intro hqbad
      exact EightEqual.paired_traps_impossible_knownSimple
        (e := e) (hz := hz) (hn := hn) hne hcard hb p hsmall hat hct hEq x hx q hq
          hqs hLgen hxpair hpbad hqbad (strict g hg)
    obtain ⟨r,hrt,hover⟩ := compatible_prepend_backward hb hat hct hcol q hqbad
    let y := g*x⁻¹
    have hy : y ∈ stabilizer d.radical (alpha d.radical) := mul_mem hg (inv_mem hx)
    have hstart : act d.radical x⁻¹ c = act d.radical y delta := by
      dsimp only [c,y]
      rw [act_mul]
    have hedge : act d.radical x⁻¹ t = act d.radical y (beta d.radical) := by
      dsimp only [t,y]
      rw [act_mul]
    have hxa' : act d.radical x⁻¹ (alpha d.radical) = alpha d.radical := inv_mem hx
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    have hend : act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2)) =
        p.walk.getVert (p.walk.length-2) := by
      rw [hlen,hq,←act_mul,mul_inv_cancel,act_one]
    have hJpull : EightEdgeComparison.edgeMover (d := d) (alpha d.radical)
        (act d.radical x⁻¹ t) = (EightEdgeComparison.edgeMover (d := d) (alpha d.radical) t).map
          (MulAut.conj x).toMonoidHom := by
      dsimp only [EightEdgeComparison.edgeMover]
      rw [SmallMover.join_map _ (MulAut.conj x).injective]
      rw [←inv_inv x,←U_act,←Q_act,←Q_act,inv_inv,hxa']
    have hfixY := hcross1
    rw [←hJpull,hedge] at hfixY
    refine ⟨y,hy,?_,?_,equalAt y hy,tripleAt y hy hfixY,strict y hy,?_,?_⟩
    · have hh := (adjacent_act_iff d.radical x⁻¹ _ _).mpr hat
      rwa [hxa',hedge] at hh
    · exact (adjacent_act_iff d.radical y _ _).mpr hdelta
    · have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hright
      rw [Subgroup.map_sup,←inv_inv x,←Q_act,←Z_act,←stabilizer_act,inv_inv,hxa',hedge,
        ←act_mul,mul_inv_cancel,act_one] at hh
      exact hh
    · have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical x⁻¹ c) (act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2))),
          w.walk.getVert 1 = act d.radical x⁻¹ t ∧
          ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2) = p.walk.getVert i := by
        refine ⟨r.act x⁻¹,?_,?_⟩
        · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act d.radical x⁻¹) hrt
        · intro i hi
          have hiq : i ≤ q.walk.length-2 := hlen.symm ▸ hi
          simp only [CriticalPath.act,actWalk_getVert,hover i hiq,hq,
            ←act_mul,mul_inv_cancel,act_one]
      rwa [hstart,hend,hedge] at hex
  · exact ⟨g,hg,hat,hct,hEq,tripleAt g hg hcross0,strict g hg,hleft,compatible_prepend_backward hb hat hct hcol p hpbad⟩


include e hz hn in
/-- Compatible backward selection at any original oriented edge. -/
theorem eight_equal_compatible_backward_at_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {a z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hgenAll : ∀ w : Vertex d.radical, color d.radical w = false →
      X d.radical w = U d.radical w ⊔
        (X d.radical w ⊓ centralizer (stabilizer d.radical w : Set (FreeAmalgam d.radical))))
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hequal : EightEdgeComparison.edgeMover (d := d) delta (p.walk.getVert 1) =
      EightEdgeComparison.edgeMover (d := d) a (p.walk.getVert 1))
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical delta)) :
    ∃ g ∈ stabilizer d.radical a,
      let c := act d.radical g delta
      let t := act d.radical g (p.walk.getVert 1)
      Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
        EightEdgeComparison.edgeMover (d := d) c t = EightEdgeComparison.edgeMover (d := d) a t ∧
        Z d.radical delta ⊓ Z d.radical a ⊓ Z d.radical c ≤
          centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
        2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical a ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hfirst : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨j,hja,hjb⟩ : ∃ j : FreeAmalgam d.radical,
      act d.radical j a = alpha d.radical ∧ act d.radical j (p.walk.getVert 1) = beta d.radical := by
    obtain ⟨j,hj|hj⟩ := edge_transitive d.radical hfirst (base_adjacent d.radical)
    · exact ⟨j,hj⟩
    · have hh := action_preserves_color d.radical j a
      rw [hj.1,p.start_color] at hh
      cases hh
  have base := eight_equal_compatible_backward_base_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb hmodel
    (z := act d.radical j z) (delta := act d.radical j delta)
  rw [←hja,←hjb] at base
  have hsmall0 : (Q d.radical (act d.radical j z)).relIndex (Z d.radical (act d.radical j a)) < 4 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hsmall
  have hstrict0 : 2 < (B d.radical (act d.radical j a) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical j delta)) := by
    rw [Escape.PairingControl.FirstPairing.B_act hb j a p.start_color,U_act,
      relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hstrict
  have equalAct (u v : Vertex d.radical) (k : FreeAmalgam d.radical) :
      EightEdgeComparison.edgeMover (d := d) (act d.radical k u) (act d.radical k v) =
        (EightEdgeComparison.edgeMover (d := d) u v).map (MulAut.conj k⁻¹).toMonoidHom := by
    dsimp only [EightEdgeComparison.edgeMover]
    rw [SmallMover.join_map _ (MulAut.conj k⁻¹).injective,U_act,Q_act,Q_act]
  have hequal0 : EightEdgeComparison.edgeMover (d := d) (act d.radical j delta)
      (act d.radical j (p.walk.getVert 1)) = EightEdgeComparison.edgeMover (d := d)
        (act d.radical j a) (act d.radical j (p.walk.getVert 1)) := by
    rw [equalAct,equalAct,hequal]
  obtain ⟨g,hg,hat,hct,heq,htriple,hi,hgen,q,hq,hover⟩ :=
    base (p.act j) hsmall0 (by simp only [CriticalPath.act,actWalk_getVert, hjb]) hgenAll ((adjacent_act_iff d.radical j _ _).mpr hdelta) hequal0 hstrict0
  have hcancel (v : Vertex d.radical) : act d.radical j⁻¹ (act d.radical j v) = v := by
    rw [←act_mul,mul_inv_cancel,act_one]
  let y := j*g*j⁻¹
  have hact (v : Vertex d.radical) :
      act d.radical j⁻¹ (act d.radical g (act d.radical j v)) = act d.radical y v := by
    simp only [←act_mul,y,mul_assoc]
  have hy : y ∈ stabilizer d.radical a := by
    change act d.radical y a = a
    rw [←hact,show act d.radical g (act d.radical j a) = act d.radical j a from hg,hcancel]
  refine ⟨y,hy,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hcancel,hact] using (adjacent_act_iff d.radical j⁻¹ _ _).mpr hat
  · simpa only [hact] using (adjacent_act_iff d.radical j⁻¹ _ _).mpr hct
  · have hh := congrArg (Subgroup.map (MulAut.conj (j⁻¹)⁻¹).toMonoidHom) heq
    rw [←equalAct,←equalAct,hact,hact,hcancel] at hh
    exact hh
  · let f := (MulAut.conj j).toMonoidHom
    have hTripleEq :
        (Z d.radical (act d.radical j delta) ⊓
          Z d.radical (act d.radical j a) ⊓ Z d.radical (act d.radical g (act d.radical j delta))).map f =
          Z d.radical delta ⊓ Z d.radical a ⊓ Z d.radical (act d.radical y delta) := by
      rw [Subgroup.map_inf _ _ f (MulAut.conj j).injective,
        Subgroup.map_inf _ _ f (MulAut.conj j).injective]
      rw [Z_act, Z_act, Z_act, map_map, map_map, map_map]
      have hc : (MulAut.conj j).toMonoidHom.comp (MulAut.conj j⁻¹).toMonoidHom = MonoidHom.id _ := by
        apply MonoidHom.ext
        intro x
        simp [MulAut.conj, mul_assoc]
      have hcy : ((MulAut.conj j).toMonoidHom.comp
          (MulAut.conj g⁻¹).toMonoidHom).comp (MulAut.conj j⁻¹).toMonoidHom =
          (MulAut.conj y⁻¹).toMonoidHom := by
        apply MonoidHom.ext
        intro x
        simp [MulAut.conj, y, mul_assoc]
      rw [hc, Subgroup.map_id]
      rw [Z_act, map_map, hcy]
      rw [Subgroup.map_id]
      rw [Z_act]
    have hh := (map_mono (f := f) htriple).trans
      (map_centralizer_le_centralizer_image _ _)
    rw [hTripleEq] at hh
    have hmap :
        Subgroup.map f (Subgroup.map (MulAut.conj j⁻¹).toMonoidHom
          (stabilizer d.radical a)) = stabilizer d.radical a := by
      rw [Subgroup.map_map]
      have hf : f.comp (MulAut.conj j⁻¹).toMonoidHom = MonoidHom.id _ := by
        apply MonoidHom.ext
        intro x
        simp [f, MulAut.conj, mul_assoc]
      rw [hf, Subgroup.map_id]
    rw [← Subgroup.coe_map] at hh
    have hmapAct : Subgroup.map f (stabilizer d.radical (act d.radical j a)) =
        Subgroup.map f (Subgroup.map (MulAut.conj j⁻¹).toMonoidHom
          (stabilizer d.radical a)) := by
      rw [stabilizer_act]
    rw [hmapAct, hmap] at hh
    exact hh
  · have hB : (B d.radical a ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj y⁻¹).toMonoidHom = B d.radical a ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        hb a p.start_color ((stabilizer d.radical a).inv_mem hy))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hstrict
  · have hh := congrArg (Subgroup.map (MulAut.conj (j⁻¹)⁻¹).toMonoidHom) hgen
    rwa [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hact,hcancel,hcancel] at hh
  · have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical j⁻¹ (act d.radical g (act d.radical j delta)))
        (act d.radical j⁻¹ ((p.act j).walk.getVert ((p.act j).walk.length-2))),
        w.walk.getVert 1 = act d.radical j⁻¹ (act d.radical g (act d.radical j (p.walk.getVert 1))) ∧
        ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2) = p.walk.getVert i := by
      refine ⟨q.act j⁻¹,?_,?_⟩
      · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act d.radical j⁻¹) hq
      · intro i hi
        have hh := congrArg (act d.radical j⁻¹) (hover i (by
          simpa only [CriticalPath.act,actWalk_length] using hi))
        simpa only [CriticalPath.act,actWalk_getVert,hcancel] using hh
    have hend : act d.radical j⁻¹ ((p.act j).walk.getVert ((p.act j).walk.length - 2)) =
        p.walk.getVert (p.walk.length - 2) := by
      simp only [CriticalPath.act, actWalk_length, actWalk_getVert]
      rw [←act_mul, mul_inv_cancel, act_one]
    rw [hend] at hex
    have hstart : act d.radical j⁻¹ (act d.radical g (act d.radical j delta)) =
        act d.radical y delta := hact delta
    have hfirst : act d.radical j⁻¹ (act d.radical g (act d.radical j (p.walk.getVert 1))) =
        act d.radical y (p.walk.getVert 1) := hact _
    rw [hstart, hfirst] at hex
    exact hex

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
