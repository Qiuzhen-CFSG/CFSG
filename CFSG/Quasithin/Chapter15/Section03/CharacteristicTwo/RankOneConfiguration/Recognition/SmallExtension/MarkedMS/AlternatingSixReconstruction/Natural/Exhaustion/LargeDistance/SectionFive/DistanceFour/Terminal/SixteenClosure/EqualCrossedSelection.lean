module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenCompatibleBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenCompatibleBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenEqual

/-!
# Retaining crossed mover generation in equal backward selection

The compatible equal-mover proof already establishes generation by the old
and selected movers in each escape orientation. This continuation retains
those equations in the actual backward witness, including for an external
strict neighbor. It keeps the source path, central triple, transporter, and
endpoint generation unchanged. The narrow private imports reuse the original
path and trapped-pair helpers without widening their public interfaces.

Source: MS93 (5.6), (5.12)(1), printed pp.917--918,924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "edgeMover" => fun a t : Vertex d.radical =>
  SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4

include e hz hn in
set_option maxHeartbeats 400000 in
private theorem equal_backward_crossed_base_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hgenAll : ∀ w : Vertex d.radical, color d.radical w = false →
      X d.radical w = U d.radical w ⊔
        (X d.radical w ⊓ centralizer (stabilizer d.radical w : Set (FreeAmalgam d.radical))))
    (hdelta : Adjacent d.radical delta (beta d.radical))
    (hequal : edgeMover delta (beta d.radical) =
      edgeMover (alpha d.radical) (beta d.radical))
    (hstrict : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical delta)) :
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      let c := act d.radical g delta
      let t := act d.radical g (beta d.radical)
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
        edgeMover c t =
          edgeMover (alpha d.radical) t ∧
        edgeMover (alpha d.radical) (beta d.radical) ⊔
          edgeMover (alpha d.radical) t = stabilizer d.radical (alpha d.radical) ∧
        Z d.radical delta ⊓ Z d.radical (alpha d.radical) ⊓ Z d.radical c ≤
          centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
        2 < (B d.radical (alpha d.radical)
          ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            c (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨t₀,hat,x,hxL,hx3,hxN,hcross0,hleft,hright,hgen,hpair,hfix⟩ :=
    SixteenSmall.sixteen_paired_original_cube_neighbor_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hfirst
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical
    (alpha d.radical) (base_adjacent d.radical) hat
  subst t₀
  rw [hfirst] at hxN hcross0
  let c := act d.radical g delta
  let t := act d.radical g (beta d.radical)
  have hx : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hxL
  have hct : Adjacent d.radical c t := (adjacent_act_iff d.radical g _ _).mpr hdelta
  have hga : act d.radical g (alpha d.radical) = alpha d.radical := hg
  have equalAt (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical (alpha d.radical)) :
      edgeMover (act d.radical y delta) (act d.radical y (beta d.radical)) =
      edgeMover (alpha d.radical) (act d.radical y (beta d.radical)) := by
    have hya : act d.radical y (alpha d.radical) = alpha d.radical := hy
    rw [←hya,mover_act,mover_act,hequal]
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
      (hfix : edgeMover (alpha d.radical) (beta d.radical) ⊔
        edgeMover (alpha d.radical) (act d.radical y (beta d.radical)) =
          stabilizer d.radical (alpha d.radical)) :
      Z d.radical delta ⊓ Z d.radical (alpha d.radical) ⊓ Z d.radical (act d.radical y delta) ≤
        centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
    have hay : Adjacent d.radical (alpha d.radical) (act d.radical y (beta d.radical)) := by
      have he : act d.radical y (alpha d.radical) = alpha d.radical := hy
      rw [←he]
      exact (adjacent_act_iff d.radical y _ _).mpr (base_adjacent d.radical)
    exact SixteenSmall.sixteen_equal_compatible_triple_central_knownSimple
      (e := e) (hz := hz) (hn := hn) hcard hb2 rfl (base_adjacent d.radical) hdelta
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
  have hgenFull : edgeMover c t ⊔ Z d.radical z ⊔
      Z d.radical (act d.radical x z) = stabilizer d.radical (alpha d.radical) := by
    rw [hEq]
    exact hgen
  have hpairFull : edgeMover c t ⊔
      (edgeMover c t).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical (alpha d.radical) := by
    rw [hEq]
    exact hpair
  have hxainv : act d.radical x⁻¹ (alpha d.radical) = alpha d.radical := inv_mem hx
  have hat₂ : Adjacent d.radical (alpha d.radical) (act d.radical x⁻¹ t) := by
    rw [←hxainv]
    exact (adjacent_act_iff d.radical x⁻¹ _ _).mpr hat
  have hct₂ : Adjacent d.radical (act d.radical x⁻¹ c) (act d.radical x⁻¹ t) :=
    (adjacent_act_iff d.radical x⁻¹ _ _).mpr hct
  have hstrict₂ : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (act d.radical x⁻¹ c)) := by
    simpa only [act_mul] using strict (g*x⁻¹) (mul_mem hg (inv_mem hx))
  have hgen₂ : Q d.radical (act d.radical x⁻¹ t) ⊔ Z d.radical z =
      stabilizer d.radical (alpha d.radical) := by
    have hh := generation_act x⁻¹ hright
    change Q d.radical (act d.radical x⁻¹ t) ⊔
      Z d.radical (act d.radical x⁻¹ (act d.radical x z)) =
        stabilizer d.radical (act d.radical x⁻¹ (alpha d.radical)) at hh
    simpa only [←act_mul,mul_inv_cancel,act_one,hxainv] using hh
  have hn₀ := SixteenEqual.generating_endpoint_does_not_normalize
    (e := e) (hz := hz) (hn := hn) hb2 hat hct hleft (strict g hg)
  have hn₂ := SixteenEqual.generating_endpoint_does_not_normalize
    (e := e) (hz := hz) (hn := hn) hb2 hat₂ hct₂ hgen₂ hstrict₂
  have hcross1 : edgeMover (alpha d.radical) (beta d.radical) ⊔
      (edgeMover (alpha d.radical) t).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical (alpha d.radical) := by
    have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hcross0
    have hxmap : (edgeMover (alpha d.radical) (beta d.radical)).map
        (MulAut.conj x).toMonoidHom = edgeMover (alpha d.radical) (beta d.radical) :=
      mem_normalizer_iff_map_conj_eq.mp hxN
    have hG : (stabilizer d.radical (alpha d.radical)).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical (alpha d.radical) :=
      mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical _).le_normalizer hx)
    rw [Subgroup.map_sup,hxmap,hG] at hh
    exact hh
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hdelta
    have hc : color d.radical delta = false := by
      change color d.radical delta ≠ true at hh
      exact Bool.eq_false_of_not_eq_true hh
    change color d.radical (act d.radical g delta) = false
    rw [action_preserves_color,hc]
  by_cases hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))
  · have hqbad : ¬ Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
      intro hqbad
      exact SixteenEqual.sixteen_equal_paired_traps_impossible_knownSimple
        (e := e) (hz := hz) (hn := hn) hb2 hcard p hsmall hat hct hEq x hx q hq
          hqs hgenFull hpairFull hpbad hqbad hn₀ hn₂ (strict g hg)
    obtain ⟨r,hrt,hover⟩ := compatible_prepend_backward hb2 hat hct hcol q hqbad
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
    have hJpull : edgeMover (alpha d.radical)
        (act d.radical x⁻¹ t) = (edgeMover (alpha d.radical) t).map
          (MulAut.conj x).toMonoidHom := by
      have hh := mover_act (d := d) x⁻¹ (alpha d.radical) t
      simpa only [inv_inv,hxa'] using hh
    have hfixY := hcross1
    rw [←hJpull,hedge] at hfixY
    refine ⟨y,hy,?_,?_,equalAt y hy,hfixY,tripleAt y hy hfixY,strict y hy,?_,?_⟩
    · simpa only [hedge] using hat₂
    · exact (adjacent_act_iff d.radical y _ _).mpr hdelta
    · simpa only [hedge] using hgen₂
    · have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical x⁻¹ c) (act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2))),
          w.walk.getVert 1 = act d.radical x⁻¹ t ∧
          ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2) = p.walk.getVert i := by
        refine ⟨r.act x⁻¹,?_,?_⟩
        · simp only [CriticalPath.act,actWalk_getVert]
          exact congrArg (act d.radical x⁻¹) hrt
        · intro i hi
          have hiq : i ≤ q.walk.length-2 := hlen.symm ▸ hi
          simp only [CriticalPath.act,actWalk_getVert,hover i hiq,hq,
            ←act_mul,mul_inv_cancel,act_one]
      rwa [hstart,hend,hedge] at hex
  · exact ⟨g,hg,hat,hct,hEq,hcross0,tripleAt g hg hcross0,strict g hg,hleft,compatible_prepend_backward hb2 hat hct hcol p hpbad⟩


include e hz hn in
/-- Compatible backward selection at any original oriented edge. -/
theorem equal_backward_crossed_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
    {a z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hgenAll : ∀ w : Vertex d.radical, color d.radical w = false →
      X d.radical w = U d.radical w ⊔
        (X d.radical w ⊓ centralizer (stabilizer d.radical w : Set (FreeAmalgam d.radical))))
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hequal : edgeMover delta (p.walk.getVert 1) =
      edgeMover a (p.walk.getVert 1))
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical delta)) :
    ∃ g ∈ stabilizer d.radical a,
      let c := act d.radical g delta
      let t := act d.radical g (p.walk.getVert 1)
      Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
        edgeMover c t = edgeMover a t ∧
        edgeMover a (p.walk.getVert 1) ⊔ edgeMover a t = stabilizer d.radical a ∧
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
  have base := equal_backward_crossed_base_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard hb
    (z := act d.radical j z) (delta := act d.radical j delta)
  rw [←hja,←hjb] at base
  have hsmall0 : (Q d.radical (act d.radical j z)).relIndex (Z d.radical (act d.radical j a)) < 4 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hsmall
  have hstrict0 : 2 < (B d.radical (act d.radical j a) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical j delta)) := by
    rw [Escape.PairingControl.FirstPairing.B_act (by omega : 2 < replacementDistance h d) j a p.start_color,U_act,
      relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hstrict
  have hequal0 : edgeMover (act d.radical j delta)
      (act d.radical j (p.walk.getVert 1)) = edgeMover
        (act d.radical j a) (act d.radical j (p.walk.getVert 1)) := by
    rw [mover_act,mover_act,hequal]
  obtain ⟨g,hg,hat,hct,heq,hcross,htriple,hi,hgen,q,hq,hover⟩ :=
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
  refine ⟨y,hy,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hcancel,hact] using (adjacent_act_iff d.radical j⁻¹ _ _).mpr hat
  · simpa only [hact] using (adjacent_act_iff d.radical j⁻¹ _ _).mpr hct
  · have hh := congrArg (Subgroup.map (MulAut.conj (j⁻¹)⁻¹).toMonoidHom) heq
    rw [←mover_act,←mover_act,hact,hact,hcancel] at hh
    exact hh
  · have hh := congrArg (Subgroup.map (MulAut.conj (j⁻¹)⁻¹).toMonoidHom) hcross
    rw [Subgroup.map_sup,←mover_act,←mover_act,←stabilizer_act,hact,hcancel,hcancel] at hh
    exact hh
  · have hh := triple_central_act (d := d) j⁻¹ htriple
    simpa only [hcancel,hact] using hh
  · have hB : (B d.radical a ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj y⁻¹).toMonoidHom = B d.radical a ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        (by omega : 2 < replacementDistance h d) a p.start_color ((stabilizer d.radical a).inv_mem hy))
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

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
