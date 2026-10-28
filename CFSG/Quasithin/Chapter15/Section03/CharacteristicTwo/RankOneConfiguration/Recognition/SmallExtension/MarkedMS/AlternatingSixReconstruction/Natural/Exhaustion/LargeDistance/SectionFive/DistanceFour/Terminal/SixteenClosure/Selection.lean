module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenSmallSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenEqualSecondBackward
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SourceKernelFailure
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenCompatibleBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenUnequal

/-!
# Source-compatible unequal backward selection for image sixteen

At distance four, an unequal strict neighbor can be transported to a
backward critical path while retaining generation by the original and
selected small movers. The selected edge comes from the existing paired
six-letter construction. Its extra generation clause is compatible with
the unequal trapped-seed exclusion, so no new trapping hypothesis is used.
Conjugating the complete construction gives the same result at any vertex.

The original and selected movers then supply the fixed-kernel clause
`C_{Z_beta}(J_alpha(T_t)) ≤ C(G_alpha)` of MS93 (5.5)(b). The actual
alpha-based selected path consumes this choice: the equal branch is
excluded, and the unequal branch retains its strict slice, both generation
identities and the nonzero moving-U/full-X failure commutator from (5.12)(1).

This is a source reduction, not the image-sixteen terminal exclusion.
Applying the fixed-kernel clause to the second failure line still requires
proving that the selected mover fixes that line. Edge containment by itself
does not prove this premise. Both moving covers and full central attachments
are retained throughout.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.5)(a,b), (5.12)(1), printed pp.915--917,924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
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
private theorem unequal_backward_base
    (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hne : SmallMover.join (U d.radical delta) (Q d.radical delta)
        (Q d.radical (p.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (p.walk.getVert 1)) 4)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        edgeMover (alpha d.radical) (p.walk.getVert 1) ⊔
          edgeMover (alpha d.radical) t = stabilizer d.radical (alpha d.radical) ∧
        edgeMover (act d.radical g delta) t ≠ edgeMover (alpha d.radical) t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g delta) (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  obtain ⟨t,hat,x,hx,hx3,hxN,hcross,hgen,_⟩ :=
    SixteenSmall.sixteen_paired_original_cube_neighbor_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hfirst
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) ha1 hat
  let c := act d.radical g delta
  have hct : Adjacent d.radical c t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g _ _).mpr hdelta
  have hga : act d.radical g (alpha d.radical) = alpha d.radical := hg
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom =
        B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 _ rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  have hi : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) := by
    change 2 < (B d.radical (alpha d.radical) _).relIndex (U d.radical (act d.radical g delta))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hstrict
  have hne' : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ≠
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical t) 4 := by
    intro he
    apply hne
    apply map_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
    rwa [SmallMover.join_map _ (MulAut.conj g⁻¹).injective,
      SmallMover.join_map _ (MulAut.conj g⁻¹).injective,←U_act,←Q_act,←Q_act,←U_act,←Q_act,hga,hgt]
  have hnorm := eligible_generating_seed_not_normalized s hb2 hat hct hgen
    (fun hh => by have he := relIndex_eq_one.mpr hh; omega)
  have hc : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  refine ⟨t,hat,g,hg,hgt,hct,hcross,hne',hgen,hi,?_⟩
  by_cases htrap : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))
  · exact (SixteenUnequal.sixteen_unequal_trapped_strict_impossible_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hat hct hne' hgen htrap hnorm hi).elim
  · let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
      .cons ((cosetGraph_adj d.radical _ _).mpr hct)
        (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
    have hw : w.length = 2 := rfl
    let q := p.prepend_two (Nat.le_of_lt hb2) hc w hw htrap
    have hqt : q.walk.getVert 1 = t := by
      simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
        hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]
    exact ⟨q,hqt,fun i hi => p.prepend_two_overlap _ _ _ _ _ hi⟩

include e hz hn in
/-- Select a literal unequal backward path while retaining generation by
the original and selected movers at its midpoint. -/
theorem unequal_backward_crossed_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
    {a z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hne : edgeMover delta (p.walk.getVert 1) ≠
      edgeMover a (p.walk.getVert 1))
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical delta)) :
    ∃ g ∈ stabilizer d.radical a,
      let c := act d.radical g delta
      let t := act d.radical g (p.walk.getVert 1)
      Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
        edgeMover c t ≠ edgeMover a t ∧
        edgeMover a (p.walk.getVert 1) ⊔ edgeMover a t = stabilizer d.radical a ∧
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
  have base := unequal_backward_base
    (e := e) (hz := hz) (hn := hn) hb hcard
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
  have hne0 : edgeMover (act d.radical j delta)
      (act d.radical j (p.walk.getVert 1)) ≠ edgeMover
        (act d.radical j a) (act d.radical j (p.walk.getVert 1)) := by
    rw [mover_act,mover_act]
    exact fun he => hne (map_injective (MulAut.conj j⁻¹).injective he)
  obtain ⟨t,hat,g,hg,hgt,hct,hcross,hne',hgen,hi,q,hq,hover⟩ :=
    base (p.act j) hsmall0 (by simp only [CriticalPath.act,actWalk_getVert])
      (by simpa only [CriticalPath.act,actWalk_getVert] using
        (adjacent_act_iff d.radical j _ _).mpr hdelta)
      (by simpa only [CriticalPath.act,actWalk_getVert] using hne0) hstrict0
  simp only [CriticalPath.act,actWalk_getVert] at hgt hcross
  rw [←hgt] at hat hct hcross hne' hgen hq
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
  · intro he
    apply hne'
    apply map_injective (f := (MulAut.conj (j⁻¹)⁻¹).toMonoidHom)
      (MulAut.conj (j⁻¹)⁻¹).injective
    rwa [←mover_act,←mover_act,hact,hact,hcancel]
  · have hh := congrArg (Subgroup.map (MulAut.conj (j⁻¹)⁻¹).toMonoidHom) hcross
    rwa [Subgroup.map_sup,←mover_act,←mover_act,←stabilizer_act,
      hcancel,hcancel,hact] at hh
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

omit [Finite G] in
/-- The fixed-kernel clause of MS93 (5.5)(b), on the two actual edge
movers. The edge omega center is fixed by the original mover; the two
movers generate the whole starting stabilizer. -/
private theorem crossed_edge_fixed_kernel
    {a b t : Vertex d.radical} (ha : color d.radical a = false)
    (hab : Adjacent d.radical a b)
    (hcross : edgeMover a b ⊔ edgeMover a t = stabilizer d.radical a) :
    Z d.radical b ⊓ centralizer (edgeMover a t : Set (FreeAmalgam d.radical)) ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  have hb : color d.radical b = true := by
    have hh := adjacent_color_ne d.radical hab
    rw [ha] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hfix : Z d.radical b ≤ centralizer (Q d.radical b : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [Z,if_neg (by simp [hb])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  apply le_centralizer_iff.mpr
  rw [←hcross]
  exact sup_le (le_centralizer_iff.mp ((inf_le_left.trans hfix).trans
    (centralizer_le (SmallMover.join_le _ _ _ _)))) (le_centralizer_iff.mp inf_le_right)

include e hz hn in
/-- The original selected path supplies an unequal backward source
configuration with the full fixed-kernel clause of (5.5)(b). The equal
case is discharged, the backward path is critical, and its source failure
line is nonzero. This is a reduction of the remaining terminal case, not
its exclusion. -/
theorem selected_source_failure_knownSimple
    (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (p.walk.getVert 2))) :
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      let c := act d.radical g (p.walk.getVert 2)
      let t := act d.radical g (p.walk.getVert 1)
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2),
        q.walk.getVert 1 = t ∧ q.walk.getVert 2 = alpha d.radical ∧
        edgeMover c t ≠ edgeMover (alpha d.radical) t ∧
        edgeMover (alpha d.radical) (p.walk.getVert 1) ⊔
          edgeMover (alpha d.radical) t = stabilizer d.radical (alpha d.radical) ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) ∧
        Z d.radical (p.walk.getVert 1) ⊓
          centralizer (edgeMover (alpha d.radical) t : Set (FreeAmalgam d.radical)) ≤
            centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
        let K := U d.radical c ⊓ Q d.radical (p.walk.getVert 2)
        let H := ⁅K,X d.radical z ⊓ Q d.radical (alpha d.radical)⁆
        Nat.card (H : Subgroup (FreeAmalgam d.radical)) = 2 ∧
          H ≤ Z d.radical c ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z ∧
          H ≤ ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ⊔
            (Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
          ¬ ⁅K,Z d.radical z⁆ ≤ ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ⊔ H := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hfirst : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hne : edgeMover (p.walk.getVert 2) (p.walk.getVert 1) ≠
      edgeMover (alpha d.radical) (p.walk.getVert 1) := by
    intro heq
    have hXall := sixteen_small_omega_centrally_generated_knownSimple
      (e := e) (hz := hz) (hn := hn) hcard hb
    have back := sixteen_equal_compatible_backward_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hcard hb p hsmall hXall hdelta heq hstrict
    rw [show p.walk.length - 2 = 2 by omega] at back
    obtain ⟨g,hg,hat,hct,heq',htriple,hi,hgen,q,hq1,hover⟩ := back
    have hq2 : q.walk.getVert 2 = alpha d.radical := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by decide)
    exact sixteen_equal_backward_strict_false_knownSimple
      (e := e) (hz := hz) (hn := hn) hcard hb p q hq2
      (by simpa only [hq1] using hgen) g hg rfl hi (by simpa only [hq1] using heq')
  have back := unequal_backward_crossed_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard hb p hsmall hdelta hne hstrict
  rw [show p.walk.length - 2 = 2 by omega] at back
  obtain ⟨g,hg,hat,hct,hne',hcross,hi,hgen,q,hq1,hover⟩ := back
  have hq2 : q.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by decide)
  refine ⟨g,hg,q,hq1,hq2,hne',hcross,hgen,hi,
    crossed_edge_fixed_kernel p.start_color hfirst hcross,?_⟩
  exact strict_small_backward_source_failure_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q hq2
    (by simpa only [hq1] using hgen) hi

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
