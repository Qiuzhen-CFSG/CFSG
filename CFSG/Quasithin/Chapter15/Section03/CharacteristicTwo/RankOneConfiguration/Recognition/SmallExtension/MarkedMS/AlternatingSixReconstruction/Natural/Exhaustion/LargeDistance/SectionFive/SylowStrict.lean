module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowEscape
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSpanCollapse
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSpanCollapse

/-!
# Strict forward slices for elementary replacement images

Above distance four, the proved elementary-image radius escape supplies an
overlapping forward critical path. If its first slice had index two, a moved
line selects one component conjugator giving both generation and noncentrality.
The existing full-cover comparison traps the shifted seed and its normal span
at the old endpoint. The seed-orbit commutator has order two; a conjugate seed
realizes it. Saturation of the whole predecessor kernel then forces the larger
orbit span into the endpoint control alternative. This makes that orbit locally
normal, and nilpotent commutator saturation collapses it to the shifted span.
Its original noncore actor now puts the seed in the Baumann subgroup, a
contradiction.

Transport and the literal backward-shift application discharge the strict-slice
premise for small critical images at every original component vertex. The
original radical may be Sylow. Both moving covers of orders sixteen and
thirty-two, every central attachment and the actual natural graph are retained.
The import-all edges reuse the internal seed-line selection and common-neighbor
seed inclusion from the same proof family without widening their public APIs.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.7)--(5.9), printed pp.919--922. SylowCritical uses this strict
bound to exclude large critical images. Terminal exclusions, non-elementary
images and distance four remain with the large-distance assembly.
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


namespace SylowStrict

include e hz hn in
/-- The small-critical-image forward slice is strict for an elementary
replacement image, including when the original radical is Sylow. -/
theorem elementary_small_forward_slice_strict_knownSimple
    (hb : 4 < replacementDistance h d)
    (hel : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  by_contra! hslice
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hesc := SylowEscape.elementary_criticalEscape_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hel
  obtain ⟨u,hu⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hel
  have hR : d.radical.map s.projection ≤ (CFSG.Quasithin.ChapterB.Offenders.D 6).map
      (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hu]
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
  obtain ⟨_,_,hT,hZcY,hYV,hYN,hYB,hHZa,_,hHCa,hcomm,hZaQ,hYQ,hDQ,hWQ⟩ :=
    cover_small_shifted_forward_configuration_of_choice s hc hb p hsmall hline.1
      z q.end_color hd y (Ltilde_le_stabilizer _ hy) hgen hmove
  let a := act d.radical y⁻¹ (alpha d.radical)
  let T₂ := T.map (MulAut.conj y).toMonoidHom
  let H₂ := H.map (MulAut.conj y).toMonoidHom
  let Y := (localZSpan d.radical c (alpha d.radical)).map (MulAut.conj y).toMonoidHom
  let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  let D := conjugateSpanBy (Z d.radical a) P
  let K := Z d.radical z ⊓ Q d.radical c
  have hyG : y ∈ stabilizer d.radical c := Ltilde_le_stabilizer c hy
  have ha : color d.radical a = false := by rw [action_preserves_color]; rfl
  have hca : (cosetGraph d.radical).dist c a = 2 := by
    have hfix : act d.radical y⁻¹ c = c := (stabilizer d.radical c).inv_mem hyG
    have hh := dist_act d.radical y⁻¹ c (alpha d.radical)
    rw [hfix,SimpleGraph.dist_comm (u := c) (v := alpha d.radical)] at hh
    exact hh.trans (p.dist_start (by omega))
  have hZaV : Z d.radical a ≤ V d.radical c := by
    have hZV : Z d.radical (alpha d.radical) ≤ V d.radical c :=
      le_iSup_of_le (alpha d.radical) (le_iSup_of_le
        (show (cosetGraph d.radical).dist (alpha d.radical) c ≤ 2 from
          (p.dist_start (by omega)).le) le_rfl)
    rw [Z_act,inv_inv]
    exact (map_mono hZV).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (DistanceEight.V_normalized d.radical _ hyG))
  have hZaB : ¬ Z d.radical a ≤ B d.radical c ((replacementGeometry h d).Z_normal _) := by
    have hBm := mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized hb2 c q.start_color hyG)
    intro he
    rw [Z_act,inv_inv,←hBm] at he
    exact critical_start_not_le_second_slice s hc hb2 p
      ((DistanceEight.U_le_Z d.radical _).trans
        ((map_le_map_iff_of_injective (MulAut.conj y).injective).mp he))
  have hDV : D ≤ V d.radical c := conjugateSpanBy_le hZaV
    (inf_le_left.trans (DistanceEight.V_normalized d.radical c))
  have hDpre : D ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
    rw [hpre]
    exact hDQ
  obtain ⟨hXgen,hA₀,hR₃,hRcard,hRseed,hRedge,hfull,hnot,halign⟩ :=
    cube_generated_span_full_kernel s hc hb2 u hR q hqsmall D P hDV hDpre
      inf_le_left (le_normalizer_conjugateSpanBy _ _) hgen
      (fun hh => hZaB ((le_conjugateSpanBy _ _).trans hh))
  have hJcard : Nat.card (⁅D,K⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
    rwa [hR₃] at hRcard
  obtain ⟨x,hx⟩ := exists_span_line_generator (Z d.radical a) P K hJcard
  let f := (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom
  have hZxD : (Z d.radical a).map f ≤ D := by
    rw [show D = conjugateSpanBy (Z d.radical a) P from rfl,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : P => (Z d.radical a).map
      (MulAut.conj (k : FreeAmalgam d.radical)).toMonoidHom) x
  have hYxW : Y.map f ≤ conjugateSpanBy Y P := by
    rw [conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : P => Y.map
      (MulAut.conj (k : FreeAmalgam d.radical)).toMonoidHom) x
  have hZxcard : Nat.card (⁅(Z d.radical a).map f,K⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
    rw [hx]
    exact hJcard
  have hsaturated := cube_predecessor_kernel_saturated s hc hb2 u hR q hqsmall
    ha hca.le Y hYV hYN hYB x x.property.1
    (by rw [hpre]; exact hZxD.trans hDQ)
    (by rw [hpre]; exact hYxW.trans hWQ) hZxcard
  have hWnot : ¬ ⁅conjugateSpanBy Y P,K⁆ ≤ ⁅(Z d.radical a).map f,K⁆ :=
    fun hle => hsaturated.2.1 ((commutator_mono hYxW le_rfl).trans hle)
  have hlen : 2 < q.walk.length := q.length_eq_b ▸ hb2
  let last := q.walk.getVert (q.walk.length-1)
  have hzlast : Adjacent d.radical z last := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-1) (by omega)
    rw [show q.walk.length-1+1=q.walk.length by omega,q.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hlastcol : color d.radical last = true := by
    cases he : color d.radical last
    · exact False.elim ((adjacent_color_ne d.radical hzlast) (q.end_color.trans he.symm))
    · rfl
  have hprelast : Adjacent d.radical a' last := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-2) (by omega)
    rw [show q.walk.length-2+1=q.walk.length-1 by omega,hpre] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hQlast : Q d.radical a' ≤ Q d.radical last := Q_le_adjacent_h d.radical hlastcol hprelast
  have hZlast : Z d.radical c ≤ Q d.radical last := by
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c q.start_color)
    rw [q.dist_start (Nat.sub_le _ _),(replacementGeometry h d).distance_constant c q.start_color]
    change q.walk.length-1 < replacementDistance h d
    have he : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  have hZxne : ⁅(Z d.radical a).map f,K⁆ ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hZxcard
    omega
  have hZxalign : ⁅(Z d.radical a).map f,K⁆ ≤
      ⁅Z d.radical c,Z d.radical z⁆ ⊔
        (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
    rw [hx,←hR₃]
    exact halign
  have hWcontrol := cube_edge_control_of_kernel_escape s hc u hR q hqsmall
    hzlast hZlast ((Z d.radical a).map f) (conjugateSpanBy Y P)
    ((hZxD.trans hDQ).trans hQlast) (hWQ.trans hQlast) hZxne hZxalign hWnot
  have hHc : H₂ ≤ Z d.radical c :=
    ((map_mono hHU).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (U_normalized c hyG))).trans (DistanceEight.U_le_Z d.radical c)
  have hQcP : Q d.radical c ≤ P :=
    le_inf (fun _ hx => hx.1)
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical c q.start_color))).trans (centralizer_le hHc))
  have hZG : Z d.radical z ≤ stabilizer d.radical c :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) c q.start_color (by
      rw [(replacementGeometry h d).distance_constant c q.start_color]
      exact replacementDistance_pos h d) q.critical
  have hcrit : ⁅Z d.radical c,Z d.radical z⁆ ≤ Z d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hZG.trans (Z_normalized d.radical c))
  have hWN : stabilizer d.radical c ≤ normalizer (conjugateSpanBy Y P : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    refine sup_le (le_normalizer_conjugateSpanBy _ _) ?_
    apply le_normalizer_iff_commutator_le_left.mpr
    exact hWcontrol.trans (sup_le
      (le_normalizer_iff_commutator_le_left.mp
        ((inf_le_right.trans hQcP).trans (le_normalizer_conjugateSpanBy _ _)))
      (hcrit.trans (hZcY.trans (le_conjugateSpanBy _ _))))
  have hcollapse : conjugateSpanBy Y P = Y :=
    small_critical_span_collapse s hc hb q hqsmall ha hca.le
      Y P hYV hYN hZcY inf_le_left hWN hWcontrol
  have hYG : stabilizer d.radical c ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rwa [hcollapse] at hWN
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
  have hcard : Nat.card H₂ = 2 := by
    rw [card_map_of_injective (MulAut.conj y).injective]
    exact hline.2.1
  have hT₂ne : ¬ T₂ ≤ Q d.radical c := by
    intro hle
    have he : ⁅U d.radical c,T₂⁆ = ⊥ := le_bot_iff.mp
      ((commutator_mono (DistanceEight.U_le_Z d.radical c) hle).trans_eq
        (Z_centralizes_Q d.radical c q.start_color))
    rw [hcommU] at he
    rw [he,card_bot] at hcard
    omega
  have hZaY : Z d.radical a ≤ Y := by
    have hh := map_mono (f := (MulAut.conj y).toMonoidHom)
      (acting_seed_le_local_span (d := d) q.start_color rfl hct hat)
    simpa only [a,Y,c,Z_act,inv_inv] using hh
  let E := conjugateSpanBy (Z d.radical a) (stabilizer d.radical c)
  have hEY : E ≤ Y := conjugateSpanBy_le hZaY hYG
  have hEV : E ≤ V d.radical c :=
    conjugateSpanBy_le hZaV (DistanceEight.V_normalized d.radical c)
  have hEB := normalized_radius_le_slice_of_actor_at s hb2 q.start_color E T₂ hEV
    (le_normalizer_conjugateSpanBy _ _) hT₂G hT₂ne
    (((commutator_mono hEY le_rfl).trans hcomm).trans hHc)
  exact hZaB ((le_conjugateSpanBy _ _).trans hEB)

/-- The strict bound on every original component vertex, with the actual
critical walk and the same second vertex. -/
theorem elementary_small_forward_slice_strict_at_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (hel : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
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
  have hi := elementary_small_forward_slice_strict_knownSimple (e := e) (hz := hz) (hn := hn) hb hel p₀ hsmall₀
  rw [hvert,U_act,inv_inv,hB,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hi
  exact hi

include e hz hn in

include e hz hn in
/-- The actual elementary-image backward shift has its strict-slice premise
proved in the small critical-image branch. Both transporters, their agreement
on the whole edge kernel, the exact index and all overlaps are retained. -/
theorem elementary_small_backward_shift_of_four_lt_knownSimple
    (hb : 4 < replacementDistance h d)
    (hel : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    ∃ t, Adjacent d.radical a t ∧
      ∃ x ∈ stabilizer d.radical a,
        act d.radical x (p.walk.getVert 1) = t ∧
        ∃ k ∈ stabilizer d.radical t,
          ∃ g ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
              stabilizer d.radical a,
            (∀ v ∈ Q d.radical t, (MulAut.conj k⁻¹) v = (MulAut.conj g) v) ∧
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
              (act d.radical k (act d.radical x (p.walk.getVert 2)))
              (p.walk.getVert (p.walk.length-2)),
            q.walk.getVert 1 = t ∧
            (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
            (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
                (U d.radical (act d.radical k (act d.radical x (p.walk.getVert 2)))) =
              (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
                (U d.radical (p.walk.getVert 2)) ∧
            2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
                (U d.radical (act d.radical k (act d.radical x (p.walk.getVert 2)))) := by
  have hstrict := elementary_small_forward_slice_strict_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hel p hsmall
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,x,hx,hxt,k,hk,g,hg,hagree,q,hqt,hover,hi⟩ :=
    SylowSmall.elementary_strict_backward_shift_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hel p hdelta hstrict
  exact ⟨t,hat,x,hx,hxt,k,hk,g,hg,hagree,q,hqt,hover,hi,hi ▸ hstrict⟩

end SylowStrict
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
