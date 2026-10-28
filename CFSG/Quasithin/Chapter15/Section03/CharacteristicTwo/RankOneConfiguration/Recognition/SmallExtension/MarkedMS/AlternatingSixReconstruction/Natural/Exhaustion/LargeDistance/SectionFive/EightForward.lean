module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightStrictShift
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowForwardSpan
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowForwardKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSpanSelection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSpanCollapse
/-!
# Strict small-image forward slices in the mixed and even image-eight branches

Radius escape supplies a forward critical extension on the actual natural
replacement graph. If the original forward slice had index at most two,
its full-core centralizer would move the next cover by a nonzero line.
Choose the residual transporter moving that line, and use the whole seed
orbit's reverse-kernel displacement to control every conjugate normal
section, including zero individual displacement. The existing nilpotent
saturation theorem collapses the full orbit span. Its whole-stabilizer
invariance then forces the escaped seed into the Baumann slice, a
contradiction. Thus the forward index is strictly greater than two.

Transport gives the strict bound at every component vertex. It discharges
the strictness premise in the mixed/even backward selector, retaining a
single transporter for the first two vertices and every overlapping walk
vertex. The original-radical application preserves index two over the
transported replacement edge core. Both moved covers, of orders sixteen
and thirty-two, and all central attachments remain.

The two-transposition mover, large critical-image and terminal comparisons,
and the general distance-four cases remain open. This module proves the
small-critical-image part of MS93 (5.9), with its actual (5.7) consumer;
it does not assert the unconditional distance bound.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.7)--(5.9), printed pp.919--922. The proof uses the already proved
natural-graph cover and orbit-span lemmas, without identifying this graph
with the exceptional original-Sylow graph.
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
  {d : Replacement L R}


namespace EightForward
open SylowForwardKernel SylowForwardSpan

include e hz hn in
/-- The small critical-image forward slice is strict in both three-duad mover
branches, without an assumed shifted configuration or orbit-span bound. -/
theorem three_duad_small_forward_slice_strict_knownSimple
    (hb : 4 < replacementDistance h d)
    (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  by_contra! hslice
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hesc := EightStrictShift.three_duad_criticalEscape_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hmodel
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T⁆
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
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
  have hline := small_forward_slice_line_knownSimple (e := e) (hz := hz) (hn := hn)
    hb2 p hslice hsmall (critical_forward_not_le_slice_of_escape s hc hb2 hesc p)
  obtain ⟨z,q,hd,hover,hpre⟩ := critical_forward_extension_of_escape s hc hb2 hesc p
  have hi := small_slice_forward_extension_index_two s hc hb p hsmall hslice
    (critical_forward_not_le_slice_of_escape s hc hb2 hesc p) q hd hpre
  have hqsmall : (Q d.radical z).relIndex (Z d.radical c) < 4 := by rw [hi]; decide
  obtain ⟨y,hy,hgen,hmove⟩ := exists_cover_line_generator s hc q H hHU
    hline.2.1 hline.2.2.2.2
  obtain ⟨_,_,hT,hZcY,hYV,hYN,hYB,hHZa,hHcard,hHCa,hcomm,hZaQ,hYQ,hDQ,hWQ⟩ :=
    cover_small_shifted_forward_configuration_of_choice s hc hb p hsmall hline.1
      z q.end_color hd y (Ltilde_le_stabilizer _ hy) hgen hmove
  let a := act d.radical y⁻¹ (alpha d.radical)
  let T₂ := T.map (MulAut.conj y).toMonoidHom
  let H₂ := H.map (MulAut.conj y).toMonoidHom
  let Y := (localZSpan d.radical c (alpha d.radical)).map (MulAut.conj y).toMonoidHom
  let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  have hyG : y ∈ stabilizer d.radical c := Ltilde_le_stabilizer c hy
  have ha : color d.radical a = false := by rw [action_preserves_color]; rfl
  have hca : (cosetGraph d.radical).dist c a = 2 := by
    have hfix : act d.radical y⁻¹ c = c := (stabilizer d.radical c).inv_mem hyG
    have hh := dist_act d.radical y⁻¹ c (alpha d.radical)
    rw [hfix,SimpleGraph.dist_comm (u := c) (v := alpha d.radical)] at hh
    exact hh.trans (p.dist_start (by omega))
  let tx := act d.radical y⁻¹ t
  have hctx : Adjacent d.radical c tx := by
    have hh := (adjacent_act_iff d.radical y⁻¹ c t).mpr hct
    rwa [show act d.radical y⁻¹ c = c from (stabilizer d.radical c).inv_mem hyG] at hh
  have hatx : Adjacent d.radical a tx := (adjacent_act_iff d.radical y⁻¹ _ _).mpr hat
  obtain ⟨hZaV,hZaB⟩ := shifted_seed_escape s hc hb p y hyG
  have hDpre : conjugateSpanBy (Z d.radical a) P ≤
      Q d.radical (q.walk.getVert (q.walk.length-2)) := by
    rw [hpre]
    exact hDQ
  have hJcard := (generated_seed_orbit_kernel_line s hc hb q hqsmall
    ha hctx hatx P inf_le_left hgen hZaB hDpre).1
  have hHcardExact : Nat.card H₂ = 2 := by
    rw [card_map_of_injective (MulAut.conj y).injective]
    exact hline.2.1
  have hZaY : Z d.radical a ≤ Y := by
    have hh := map_mono (f := (MulAut.conj y).toMonoidHom)
      (acting_seed_le_local_span (d := d) q.start_color rfl hct hat)
    simpa only [a,Y,c,Z_act,inv_inv] using hh
  have hWpre : conjugateSpanBy Y P ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
    rw [hpre]
    exact hWQ
  have hcomm' : ⁅Y,Q d.radical a ⊓ centralizer
      (U d.radical c ⊓ B d.radical a ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))⁆ ≤ H₂ := by
    rw [←hT]
    exact hcomm
  have hcollapse := shifted_span_collapse s hc hb q (by rw [hi]; decide) ha hca.le
    Y H₂ P hYV hYN hYB hZaY hZcY inf_le_left inf_le_right hgen hHcardExact hmove hcomm' hJcard hWpre
  have hYG : stabilizer d.radical c ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hcollapse.2.2]
    exact hcollapse.1
  have hHc : H₂ ≤ Z d.radical c :=
    ((map_mono hHU).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (U_normalized c hyG))).trans (DistanceEight.U_le_Z d.radical c)
  have hT₂G : T₂ ≤ stabilizer d.radical c :=
    (show T₂ ≤ Q d.radical a by
      change T₂ = Q d.radical a ⊓ _ at hT
      rw [hT]
      exact inf_le_left).trans
      (Q_le_stabilizer_of_dist_le_two a c ha q.start_color (by rw [SimpleGraph.dist_comm]; exact hca.le))
  have hcommU : ⁅U d.radical c,T₂⁆ = H₂ := by
    have hUm : (U d.radical c).map (MulAut.conj y).toMonoidHom = U d.radical c :=
      mem_normalizer_iff_map_conj_eq.mp (U_normalized c hyG)
    dsimp only [H₂,H]
    rw [map_commutator,hUm]
  have hT₂ne : ¬ T₂ ≤ Q d.radical c := by
    intro hle
    have he : ⁅U d.radical c,T₂⁆ = ⊥ := le_bot_iff.mp
      ((commutator_mono (DistanceEight.U_le_Z d.radical c) hle).trans_eq
        (Z_centralizes_Q d.radical c q.start_color))
    rw [hcommU] at he
    rw [he,card_bot] at hHcardExact
    omega
  let E := conjugateSpanBy (Z d.radical a) (stabilizer d.radical c)
  have hEY : E ≤ Y := conjugateSpanBy_le hZaY hYG
  have hEV : E ≤ V d.radical c :=
    conjugateSpanBy_le hZaV (DistanceEight.V_normalized d.radical c)
  have hEB := normalized_radius_le_slice_of_actor_at s hb2 q.start_color E T₂ hEV
    (le_normalizer_conjugateSpanBy _ _) hT₂G hT₂ne
    (((commutator_mono hEY le_rfl).trans hcomm).trans hHc)
  exact hZaB ((le_conjugateSpanBy _ _).trans hEB)

include e hz hn in
/-- The same strict slice at every component vertex of the natural graph. -/
theorem three_duad_small_forward_slice_strict_at_knownSimple
    (hb : 4 < replacementDistance h d)
    (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g⁻¹ a) (act d.radical g⁻¹ a'),
      p₀.walk.getVert 2 = act d.radical g⁻¹ (p.walk.getVert 2) :=
    ⟨p.act g⁻¹,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hvert⟩ := hpact
  have hsmall₀ : (Q d.radical (act d.radical g⁻¹ a')).relIndex
      (Z d.radical (alpha d.radical)) < 4 := by
    rw [←hbase,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹⁻¹).injective]
    exact hsmall
  have hB := Escape.PairingControl.FirstPairing.B_act
    (geometry := replacementGeometry h d) (by change 2 < replacementDistance h d; omega)
    g⁻¹ a p.start_color
  rw [hbase,inv_inv] at hB
  have hi := three_duad_small_forward_slice_strict_knownSimple (e := e) (hz := hz) (hn := hn) hb hmodel p₀ hsmall₀
  rw [hvert,U_act,inv_inv,hB,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hi
  exact hi

include e hz hn in
/-- Strict backward selection for every actual small critical path. The same
starting-stabilizer element transports both of the first two vertices. -/
theorem three_duad_small_backward_step_knownSimple
    (hb : 4 < replacementDistance h d)
    (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4) :
    ∃ x ∈ stabilizer d.radical a,
      let c := act d.radical x (p.walk.getVert 2)
      let t := act d.radical x (p.walk.getVert 1)
      Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
        2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) c
            (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hl : 4 < p.walk.length := p.length_eq_b ▸ hb
  have ha1 : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have h21 : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨g,hg|hg⟩ := edge_transitive d.radical ha1 (base_adjacent d.radical)
  · change act d.radical g a = alpha d.radical ∧
      act d.radical g (p.walk.getVert 1) = beta d.radical at hg
    have base := EightStrictShift.three_duad_strict_backward_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hmodel
      (z := act d.radical g z) (delta := act d.radical g (p.walk.getVert 2))
    rw [←hg.1,←hg.2] at base
    have hsmall' : (Q d.radical (act d.radical g z)).relIndex
        (Z d.radical (act d.radical g a)) < 4 := by
      rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
      exact hsmall
    have hstrict := three_duad_small_forward_slice_strict_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hmodel (p.act g) hsmall'
    simp only [CriticalPath.act,actWalk_getVert] at hstrict
    obtain ⟨x,hx,hat,hct,hi,q,hq1,hover⟩ := base (p.act g) hsmall'
      ((adjacent_act_iff d.radical g _ _).mpr h21) hstrict
    let y := g*x*g⁻¹
    have hy (v : Vertex d.radical) :
        act d.radical y v = act d.radical g⁻¹ (act d.radical x (act d.radical g v)) := by
      simp only [y,act_mul]
    have hcancel (v : Vertex d.radical) : act d.radical g⁻¹ (act d.radical g v) = v := by
      rw [←act_mul,mul_inv_cancel,act_one]
    have hqc : ∃ r : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical y (p.walk.getVert 2)) (p.walk.getVert (p.walk.length-2)),
        r.walk.getVert 1 = act d.radical y (p.walk.getVert 1) ∧
        ∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i := by
      have hh : ∃ r : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical g⁻¹ (act d.radical x (act d.radical g (p.walk.getVert 2))))
          (act d.radical g⁻¹ ((p.act g).walk.getVert ((p.act g).walk.length-2))),
          r.walk.getVert 1 = act d.radical g⁻¹ (act d.radical x (act d.radical g (p.walk.getVert 1))) ∧
          ∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i := by
        refine ⟨q.act g⁻¹,?_,?_⟩
        · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act d.radical g⁻¹) hq1
        · intro i hi
          have he := congrArg (act d.radical g⁻¹) (hover i (by
            simpa only [CriticalPath.act,actWalk_length] using hi))
          simpa only [CriticalPath.act,actWalk_getVert,hcancel] using he
      have hend : act d.radical g⁻¹ ((p.act g).walk.getVert ((p.act g).walk.length-2)) =
          p.walk.getVert (p.walk.length-2) := by
        change act d.radical g⁻¹ ((actWalk d.radical g p.walk).getVert
          ((actWalk d.radical g p.walk).length-2)) = _
        rw [actWalk_length,actWalk_getVert,hcancel]
      rw [hend,←hy,←hy] at hh
      exact hh
    refine ⟨y,?_,?_,?_,?_,hqc⟩
    · change act d.radical y a = a
      rw [hy,show act d.radical x (act d.radical g a) = act d.radical g a from hx,hcancel]
    · simpa only [hy,hcancel] using (adjacent_act_iff d.radical g⁻¹ _ _).mpr hat
    · simpa only [hy] using (adjacent_act_iff d.radical g⁻¹ _ _).mpr hct
    · have hBi := Escape.PairingControl.FirstPairing.B_act
        (geometry := replacementGeometry h d) (by omega : 2 < replacementDistance h d)
        g a p.start_color
      have hh := hi
      rw [hBi] at hh
      have hUy : (U d.radical (act d.radical y (p.walk.getVert 2))).map
          (MulAut.conj g⁻¹).toMonoidHom =
          U d.radical (act d.radical x (act d.radical g (p.walk.getVert 2))) := by
        rw [←U_act,hy,←act_mul,inv_mul_cancel,act_one]
      rw [←hUy,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at hh
      exact hh
  · have ht : color d.radical (beta d.radical) = false := by
      change color d.radical (hVertex d.radical 1) = false
      rw [←hg.1,action_preserves_color,p.start_color]
    cases ht

include e hz hn in
/-- The original MS radical retains index two over the selected replacement
edge core, and the strict source shift retains the same conjugator and walk. -/
theorem original_radical_three_duad_strict_backward_knownSimple
    (hb : 4 < replacementDistance h d)
    (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    ∃ x ∈ stabilizer d.radical (alpha d.radical),
      let c := act d.radical x (p.walk.getVert 2)
      let t := act d.radical x (beta d.radical)
      (Q d.radical t).relIndex (T.map (MulAut.conj x⁻¹).toMonoidHom) = 2 ∧
        Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) c
            (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  obtain ⟨x,hx,hat,hct,hi,q,hq1,hover⟩ := three_duad_small_backward_step_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hmodel p hsmall
  rw [hfirst] at hat hct hq1
  refine ⟨x,hx,?_,hat,hct,hi,q,hq1,hover⟩
  rw [Q_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective,
    Q_beta,relIndex_map_map_of_injective _ _ (embedM_injective d.radical)]
  exact (SylowWholeCore.four_lt_original_sylow_eight_image_knownSimple
    (e := e) (hz := hz) (hn := hn) hb).2.2.1

end EightForward
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
