module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.ResidualRotation
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ElementaryKernelControl

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelMovement
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSmallSeeds

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SelectedFour

/-!
# Source normalization and initial selection at distance four

A backward seed in the midpoint two-core, joined with the starting seed,
is elementary abelian. If the critical endpoint does not normalize that
join, the full-cover action calculation gives a nonzero aligned commutator
of order two with the full critical kernel. The residual rotation therefore
supplies a nonabelian large-slice critical path whenever the predecessor
slice is small. Both moving covers and the entire central attachment remain.

The incident full-seed index is at most eight already above distance two.
Thus source generation by an edge kernel and the critical endpoint makes
an eligible neighboring seed span nonnormal. Its literal application
constructs the nonzero aligned mover needed by the rotation argument.

More generally, a small predecessor slice alone suffices for initial
selection. For an eligible neighboring seed whose orbit span is trapped in
the midpoint core, rotation forces the endpoint to normalize every conjugate
seed span. The normal core of the span normalizer contains the critical
transposition and the whole symmetric quotient. The index-eight normal
section then lies in the Baumann slice, contradicting eligibility.

This first gives selection from an eligible forward seed: otherwise its
selected span is abelian and therefore trapped. If the whole starting radius
is trapped, the existing eligible-neighbor theorem supplies a trapped orbit
span. Otherwise radius escape constructs a reciprocal critical path, which
makes the original forward seed eligible. No backward mover, generating
edge, radical-image restriction or cover restriction is assumed.

Transport and reversal apply this argument to either endpoint of every
critical path. The remaining initial-selection alternative has both endpoint
midpoint-slice indices greater than two on every critical path. Excluding
that alternative, the independently owned selected terminal family and
DistanceFourInput assembly remain source obligations.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), (5.7)--(5.8), printed pp.866--867 and 919--920, and
its use at the start of (5.12), p.924. The private imports reuse the checked
full-cover fixed-index, edge-coordinate, small-section and normal-subgroup
calculations at their actual hypotheses, preserving their public boundaries.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- Source normalization failure gives an actual nonzero aligned line in
the full backward critical kernel, without a radical-image restriction. -/
theorem nonnormal_backward_kernel_line
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a z delta t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hdelta : Adjacent d.radical delta t)
    (hD : Z d.radical delta ≤ Q d.radical (p.walk.getVert 2))
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical delta ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical))) :
    Nat.card (⁅Z d.radical z ⊓ Q d.radical a,Z d.radical delta⁆ :
      Subgroup (FreeAmalgam d.radical)) = 2 ∧
    ⁅Z d.radical z ⊓ Q d.radical a,Z d.radical delta⁆ ≤
      ⁅Z d.radical a,Z d.radical z⁆ ⊔
        (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z :
          Set (FreeAmalgam d.radical))) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases he : color d.radical t <;> simp_all
  have hdeltaCol : color d.radical delta = false := by
    have hh := adjacent_color_ne d.radical hdelta
    rw [ht] at hh
    cases he : color d.radical delta <;> simp_all
  have hdist : (cosetGraph d.radical).dist delta a ≤ 2 := by
    have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hdelta)
    have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    have hh := (cosetGraph_connected d.radical).dist_triangle (u := delta) (v := t) (w := a)
    omega
  have hDQa : Z d.radical delta ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical delta
      ((replacementGeometry h d).exists_critical delta hdeltaCol)
    rw [(replacementGeometry h d).distance_constant delta hdeltaCol]
    change (cosetGraph d.radical).dist delta a < replacementDistance h d
    omega
  have hDV : Z d.radical delta ≤ V d.radical a :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)
  have hDG : Z d.radical delta ≤ stabilizer d.radical a := hDQa.trans (fun _ hx => hx.1)
  have hQaD : Q d.radical a ≤ stabilizer d.radical delta :=
    (Q_le_adjacent_h d.radical ht hat).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hdelta))
  have hzt : Adjacent d.radical z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hAlast : Z d.radical a ≤ Q d.radical (p.walk.getVert 3) := by
    apply Z_le_Q_of_dist_lt d.radical a
      ((replacementGeometry h d).exists_critical a p.start_color)
    rw [(replacementGeometry h d).distance_constant a p.start_color,p.dist_start (by omega)]
    exact show 3 < replacementDistance h d by omega
  have hcCol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hlastCol : color d.radical (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [hcCol] at hh
    cases he : color d.radical (p.walk.getVert 3) <;> simp_all
  have hDlast : Z d.radical delta ≤ Q d.radical (p.walk.getVert 3) :=
    hD.trans (Q_le_adjacent_h d.radical hlastCol hct)
  let K := Z d.radical z ⊓ Q d.radical a
  let P := Z d.radical delta ⊔ Z d.radical a
  let N := ⁅K,P⁆
  let H := ⁅K,Z d.radical delta⁆
  have hKN : K ≤ normalizer (P : Set (FreeAmalgam d.radical)) :=
    (le_inf ((inf_le_right.trans hQaD).trans (Z_normalized d.radical delta))
      ((inf_le_right.trans (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1)).trans (Z_normalized d.radical a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hNP : N ≤ P := by
    change ⁅K,P⁆ ≤ P
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hKN
  have hHN : H ≤ N := commutator_mono le_rfl le_sup_left
  have hcrit : ⁅Z d.radical z,Z d.radical a⁆ ≤ Z d.radical a := by
    rw [commutator_comm]
    exact ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical a)
  have hfixed : K = Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color)))
    · apply le_inf inf_le_left
      rw [←C_eq_Q s hc a p.start_color]
      exact le_inf (inf_le_left.trans (critical_Z_le_stabilizer d.radical
        (replacementGeometry h d) a p.start_color (by
          rw [(replacementGeometry h d).distance_constant a p.start_color]
          exact replacementDistance_pos h d) p.critical)) inf_le_right
  have hfail : ¬ ⁅Z d.radical z,P⁆ ≤
      ⁅Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)),P⁆ ⊔
        ⁅Z d.radical z,Z d.radical a⁆ := by
    rw [←hfixed]
    intro hh
    apply hnorm
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [commutator_comm]
    exact hh.trans (sup_le hNP (hcrit.trans le_sup_right))
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) delta hdeltaCol
  have hPelem : IsElementaryAbelian 2 P :=
    IsElementaryAbelian.sup_of_le_centralizer
      ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a p.start_color)).trans
        (centralizer_le hDQa))
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
  have hindex : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ 2 := by
    have hQC := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc p hsmall).2
  have hbounds := elementary_edge_kernel_small_aligned s hc p.end_color hzt
    (Z d.radical a) P hAlast (sup_le hDlast hAlast) le_sup_right hPelem
    p.critical.2 hindex hfail
  rw [←hfixed] at hbounds
  have hne : H ≠ ⊥ := by
    intro hzero
    have hfix := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
    have hmove := small_critical_predecessor_commutator s hc hb2 p hsmall
      (Z d.radical delta) (by simpa only [hl] using hD) hfix
    have htotal := commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      (Z d.radical delta) (Z d.radical a) (Z d.radical z) (Z d.radical a)
      (Z_normalized d.radical a) hDG (Z_le_stabilizer d.radical a) hmove
      (by rwa [commutator_comm] at hcrit)
    exact hnorm (le_normalizer_iff_commutator_le_left.mpr (htotal.trans le_sup_right))
  let := finite_stabilizer d.radical a
  have hPG : P ≤ stabilizer d.radical a := sup_le hDG (Z_le_stabilizer d.radical a)
  let : Finite N := Finite.of_injective (inclusion (hNP.trans hPG)) (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion hHN) (inclusion_injective _)
  have hupper := (card_le_of_le hHN).trans hbounds.1
  have hlower := (one_lt_card_iff_ne_bot H).mpr hne
  refine ⟨by change Nat.card H = 2; omega,?_⟩
  exact (hHN.trans hbounds.2).trans (sup_le_sup
    (by rw [commutator_comm]) (inf_le_inf_right _ (Z_le_stabilizer d.radical z)))

include e hz hn in
/-- The actual small-predecessor initial-selection step needs only the source
normalization failure. Its nonzero aligned kernel line is constructed above. -/
theorem initial_selection_of_small_predecessor_nonnormal_knownSimple
    (hb : replacementDistance h d = 4) {a z delta t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hslice : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2)
    (hat : Adjacent d.radical a t) (hdelta : Adjacent d.radical delta t)
    (hD : Z d.radical delta ≤ Q d.radical (p.walk.getVert 2))
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical delta ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical))) :
    ∃ w, ∃ r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) w,
      ⁅localZSpan d.radical (r.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (r.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (r.walk.getVert 2)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hs := critical_predecessor_slice_eq_kernel s hc hb2 p (by simpa only [hl] using hslice)
  have hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4 := by rw [hs.2.1]; decide
  obtain ⟨hcard,halign⟩ := nonnormal_backward_kernel_line s hc hb p hsmall hat hdelta hD hnorm
  apply initial_selection_of_aligned_kernel_movement_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hslice hat hdelta hD _ halign
  intro he
  rw [he,card_bot] at hcard
  omega

include e hz hn in
private theorem edge_fixed_index_le_eight
    (hb : 2 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical a) ≤ 8 := by
  let T := Q d.radical t
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨i,hinj,hir,hiR,_,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hc ha hat
  have hTS : T ≤ stabilizer d.radical a := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hm : (T.comap i).map i = T := map_comap_eq_self (hTS.trans_eq hir.symm)
  have hTR : T.comap i ≤ d.radical := by
    have hh := comap_mono (f := i) (show T ≤ Q d.radical t from le_rfl)
    rwa [←hiR,comap_map_eq_self_of_injective hinj] at hh
  have hiT : (centralizer (T : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ 8 := by
    have hidx := SmallMover.centralizer_index_map i hinj (replacementMoved d) (T.comap i)
    rw [hiU,hm] at hidx
    rw [hidx]
    let := replacementMoved_normal h d
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (SylowKernelMovement.cover_two_group_fixed_bound s _
        ((replacement_radical_isPGroup h d).of_injective (inclusion hTR)
          (inclusion_injective hTR)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all
  have hedge : Z d.radical t ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
    intro z hz
    rw [Z,if_neg (by simp [ht])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2
  let C := Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical))
  have hCZ : C ≤ Z d.radical a := inf_le_left
  let : Finite C := Finite.of_injective (inclusion hCZ) (inclusion_injective _)
  have hnorm : C ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans (Z_le_stabilizer d.radical a)).trans (U_normalized a)
  have hjoin : U d.radical a ⊔ C = Z d.radical a := by
    apply le_antisymm (sup_le (DistanceEight.U_le_Z d.radical a) hCZ)
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d ha hat]
    exact sup_le le_sup_left (le_sup_right.trans' (le_inf
      (adjacent_Z_le d.radical ha hat) hedge))
  have hindex := relIndex_sup_of_normalizes (U d.radical a) C hnorm
  rw [hjoin] at hindex
  change (Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical))).relIndex
    (Z d.radical a) = C.relIndex (U d.radical a) at hindex
  rw [inf_relIndex_left] at hindex
  have hCU : C ⊓ U d.radical a = centralizer (T : Set (FreeAmalgam d.radical)) ⊓ U d.radical a := by
    ext z
    exact ⟨fun hz => ⟨hz.1.2,hz.2⟩,fun hz => ⟨⟨DistanceEight.U_le_Z d.radical a hz.2,hz.1⟩,hz.2⟩⟩
  rw [hindex,←inf_relIndex_right C,hCU,inf_relIndex_right]
  exact hiT

include e hz hn in
/-- The full seed has index at most eight over the actual incident edge seed. -/
private theorem edge_seed_index_le_eight
    (hb : 2 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    (Z d.radical t).relIndex (Z d.radical a) ≤ 8 := by
  let := finite_Z d.radical a
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a ha
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all
  have hZaQ : Z d.radical a ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ ha)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ ha]
    exact replacementDistance_pos h d
  have hZaT := hZaQ.trans (Q_le_adjacent_h d.radical ht hat)
  have hCZ : Z d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) ≤
      Z d.radical t := by
    intro z hz
    rw [Z,if_neg (by simp [ht])]
    exact mem_omegaCenter_iff.mpr ⟨hZaT hz.1,
      elemPow_eq_one_of_isElementaryAbelian z hz.1,hz.2⟩
  have hi := edge_fixed_index_le_eight
    (e := e) (hz := hz) (hn := hn) hb ha hat
  have hle := relIndex_le_of_le_left hCZ
    (index_ne_zero_of_finite : (Z d.radical a ⊓ centralizer
      (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a) ≠ 0)
  rw [inf_relIndex_left] at hle
  exact hle.trans hi

include e hz hn in
/-- The adjacent-seed span has index at most eight over the starting seed. -/
private theorem adjacent_seed_span_index_le_eight
    (hb : 2 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    (Z d.radical a).relIndex (Z d.radical c ⊔ Z d.radical a) ≤ 8 := by
  have hc : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [ha] at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all
  have hZaQ : Z d.radical a ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ ha)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ ha]
    exact replacementDistance_pos h d
  have hZaN : Z d.radical a ≤ normalizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    (hZaQ.trans (Q_le_adjacent_h d.radical ht hat)).trans
      ((show Q d.radical t ≤ stabilizer d.radical c from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c))
  let := finite_Z d.radical c
  let := finite_Z d.radical a
  rw [relIndex_sup_of_normalizes _ _ hZaN]
  exact (relIndex_le_of_le_left (adjacent_Z_le d.radical ha hat)
    index_ne_zero_of_finite).trans (edge_seed_index_le_eight (e := e) (hz := hz) (hn := hn) hb hc hct)


include s in
/-- Source edge generation makes an eligible full seed span nonnormal. The
order-eight section bound holds on both covers already above distance two. -/
theorem eligible_generating_seed_not_normalized
    (hb : 2 < replacementDistance h d) {z delta t : Vertex d.radical}
    (hat : Adjacent d.radical (alpha d.radical) t)
    (hdelta : Adjacent d.radical delta t)
    (hgen : Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical))
    (hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ¬ Z d.radical z ≤ normalizer
      ((Z d.radical delta ⊔ Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)) := by
  intro hnorm
  let Y := Z d.radical delta ⊔ Z d.radical (alpha d.radical)
  have hYN : stabilizer d.radical (alpha d.radical) ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    refine sup_le ?_ hnorm
    exact (le_inf
      ((show Q d.radical t ≤ stabilizer d.radical delta from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hdelta)).trans (Z_normalized d.radical delta))
      ((show Q d.radical t ≤ stabilizer d.radical (alpha d.radical) from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans (Z_normalized d.radical _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hdist : (cosetGraph d.radical).dist delta (alpha d.radical) ≤ 2 := by
    have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hdelta)
    have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    have hh := (cosetGraph_connected d.radical).dist_triangle (u := delta) (v := t) (w := alpha d.radical)
    omega
  have hYV : Y ≤ V d.radical (alpha d.radical) :=
    sup_le ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist))
      (Z_le_VBall d.radical _ 2)
  exact hel ((DistanceEight.U_le_Z d.radical delta).trans (le_sup_left.trans
    (normal_small_radius_le_slice s hb Y hYV hYN
      (adjacent_seed_span_index_le_eight (e := e) (hz := hz) (hn := hn) hb rfl hat hdelta))))

include e hz hn in
/-- Construct the nonzero aligned mover from source edge generation and an
eligible trapped seed, then apply the same original residual rotation. -/
theorem initial_selection_of_small_predecessor_generating_edge_knownSimple
    (hb : replacementDistance h d = 4) {z delta t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hslice : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2)
    (hat : Adjacent d.radical (alpha d.radical) t) (hdelta : Adjacent d.radical delta t)
    (hgen : Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical))
    (hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _))
    (hD : Z d.radical delta ≤ Q d.radical (p.walk.getVert 2)) :
    ∃ w, ∃ r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) w,
      ⁅localZSpan d.radical (r.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (r.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (r.walk.getVert 2)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  exact initial_selection_of_small_predecessor_nonnormal_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hslice hat hdelta hD
    (eligible_generating_seed_not_normalized s (by omega) hat hdelta hgen hel)


include e hz hn in
/-- An eligible neighbor whose entire orbit span is trapped at the midpoint
supplies initial selection when the endpoint has a small predecessor slice. -/
theorem initial_selection_of_eligible_trapped_small_predecessor_knownSimple
    (hb : replacementDistance h d = 4) {z delta t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hslice : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2)
    (hat : Adjacent d.radical (alpha d.radical) t)
    (hct : Adjacent d.radical delta t)
    (hel : ¬ U d.radical delta ≤
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _))
    (hPQ : localZSpan d.radical delta (alpha d.radical) ≤ Q d.radical (p.walk.getVert 2)) :
    ∃ w, ∃ r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) w,
      ⁅localZSpan d.radical (r.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (r.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (r.walk.getVert 2)) := by
  classical
  by_contra hno
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let P := localZSpan d.radical delta (alpha d.radical)
  have hdist : (cosetGraph d.radical).dist delta (alpha d.radical) ≤ 2 := by
    have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    have hh := (cosetGraph_connected d.radical).dist_triangle
      (u := delta) (v := t) (w := alpha d.radical)
    omega
  have hPV : P ≤ V d.radical (alpha d.radical) := localZSpan_le_V d.radical hdist
  have hQaGc : Q d.radical (alpha d.radical) ≤ stabilizer d.radical delta := by
    have ht : color d.radical t = true := by
      have hh := adjacent_color_ne d.radical hat
      change false ≠ color d.radical t at hh
      cases he : color d.radical t <;> simp_all
    exact (Q_le_adjacent_h d.radical ht hat).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hpair (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (alpha d.radical)) :
      Z d.radical z ≤ normalizer
        ((Z d.radical (act d.radical g delta) ⊔ Z d.radical (alpha d.radical) :
          Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    by_contra hnorm
    have hga : act d.radical g (alpha d.radical) = alpha d.radical := hg
    have hag : Adjacent d.radical (alpha d.radical) (act d.radical g t) := by
      rw [←hga]
      exact (adjacent_act_iff d.radical g _ _).mpr hat
    have hcg := (adjacent_act_iff d.radical g _ _).mpr hct
    have hZP : Z d.radical (act d.radical g delta) ≤ P := by
      rw [Z_act]
      exact (map_mono (Z_le_localZSpan d.radical delta (alpha d.radical))).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized d.radical delta (alpha d.radical)
          ((stabilizer d.radical (alpha d.radical)).inv_mem hg)))
    exact hno (initial_selection_of_small_predecessor_nonnormal_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hslice hag hcg (hZP.trans hPQ) hnorm)
  let D := Z d.radical delta ⊔ Z d.radical (alpha d.radical)
  let f := embedM d.radical
  let D₀ := D.comap f
  let A₀ := (Z d.radical z).comap f
  let N := (normalizer (D₀ : Set d.overgroup)).normalCore
  have hDV : D ≤ V d.radical (alpha d.radical) :=
    sup_le ((Z_le_localZSpan d.radical _ _).trans hPV) (Z_le_VBall d.radical _ 2)
  have hDG : D ≤ f.range := (hDV.trans ((replacementGeometry h d).V_local _ rfl hb2)).trans_eq
    (stabilizer_m_base d.radical)
  have hDm : D₀.map f = D := map_comap_eq_self hDG
  have hDc : (normalizer (D : Set (FreeAmalgam d.radical))).comap f =
      normalizer (D₀ : Set d.overgroup) := comap_normalizer_eq_of_le_range hDG
  have hg (m : d.overgroup) : f m ∈ stabilizer d.radical (alpha d.radical) := by
    change f m ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  have hQaN : Q d.radical (alpha d.radical) ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    (le_inf (hQaGc.trans (Z_normalized d.radical delta))
      ((show Q d.radical (alpha d.radical) ≤ stabilizer d.radical (alpha d.radical) from
        fun _ hx => hx.1).trans (Z_normalized d.radical _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hkN : pCore 2 d.overgroup ≤ N := by
    apply normal_le_normalCore.mpr
    rw [←hDc]
    intro k hk
    apply hQaN
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    exact mem_map_of_mem f hk
  have hAN : A₀ ≤ N := by
    intro k hk m
    rw [←hDc]
    change f (m*k*m⁻¹) ∈ normalizer (D : Set (FreeAmalgam d.radical))
    let g := f m
    have hga : act d.radical g (alpha d.radical) = alpha d.radical := hg m
    have hmapD : D.map (MulAut.conj g⁻¹).toMonoidHom =
        Z d.radical (act d.radical g delta) ⊔ Z d.radical (alpha d.radical) := by
      dsimp only [D]
      rw [Subgroup.map_sup,←Z_act,←Z_act,hga]
    have hkn : f k ∈ normalizer (D.map (MulAut.conj g⁻¹).toMonoidHom :
        Set (FreeAmalgam d.radical)) := by
      rw [hmapD]
      exact hpair g (hg m) hk
    have hm := (D.map (MulAut.conj g⁻¹).toMonoidHom).le_normalizer_map
      (MulAut.conj g).toMonoidHom (mem_map_of_mem (MulAut.conj g).toMonoidHom hkn)
    have hid : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id (FreeAmalgam d.radical) := by
      apply MonoidHom.ext
      intro y
      change g * (g⁻¹*y*(g⁻¹)⁻¹)*g⁻¹ = y
      group
    rw [map_map,hid,map_id] at hm
    change g * f k * g⁻¹ ∈ normalizer (D : Set (FreeAmalgam d.radical)) at hm
    simpa only [map_mul,map_inv] using hm
  have hs := critical_predecessor_slice_eq_kernel s hc hb2 p (by simpa only [hl] using hslice)
  have hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 := by
    rw [hs.2.1]
    decide
  have htop : N = ⊤ := by
    apply normal_eq_top_of_odd_image s N hkN
    intro heven
    obtain ⟨v,hv,hAv⟩ := small_critical_image_eq_swap s hc p hsmall
    have hvA : v ∈ A₀.map s.projection := by
      change v ∈ graphImage s (Z d.radical z)
      rw [hAv]
      exact mem_zpowers v
    have he := Equiv.Perm.mem_alternatingGroup.mp (heven ((map_mono hAN) hvA))
    rw [hv.sign_eq] at he
    exact (by decide : (-1 : ℤˣ) ≠ 1) he
  have hDN : stabilizer d.radical (alpha d.radical) ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
    intro x hx
    obtain ⟨k,rfl⟩ := (stabilizer_m_base d.radical).le hx
    have hkN : k ∈ N := by rw [htop]; exact mem_top k
    have hk : k ∈ normalizer (D₀ : Set d.overgroup) :=
      (normalizer (D₀ : Set d.overgroup)).normalCore_le hkN
    have hm := D₀.le_normalizer_map f (mem_map_of_mem f hk)
    rwa [hDm] at hm
  exact hel ((DistanceEight.U_le_Z d.radical delta).trans (le_sup_left.trans
    (normal_small_radius_le_slice s hb2 D hDV hDN
      (adjacent_seed_span_index_le_eight (e := e) (hz := hz) (hn := hn) hb2 rfl hat hct))))


include e hz hn in
/-- An eligible forward seed and a small predecessor slice produce initial
selection on every original radical image and both covers. If the selected
span were abelian, every conjugate seed would stay in the midpoint core.
Residual rotation then makes every conjugate seed span invariant under the
critical endpoint. The normal core of its normalizer contains the critical
transposition and hence the whole symmetric quotient, contradicting eligibility. -/
theorem initial_selection_of_eligible_small_predecessor_knownSimple
    (hb : replacementDistance h d = 4) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hslice : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2)
    (hel : ¬ U d.radical (p.walk.getVert 2) ≤
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ∃ w, ∃ r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) w,
      ⁅localZSpan d.radical (r.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (r.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (r.walk.getVert 2)) := by
  classical
  by_contra hno
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan d.radical c (alpha d.radical)
  have hcCol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hac : (cosetGraph d.radical).dist (alpha d.radical) c = 2 := p.dist_start (by omega)
  have hca : (cosetGraph d.radical).dist c (alpha d.radical) = 2 := by rw [SimpleGraph.dist_comm,hac]
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hPab : ⁅P,P⁆ = ⊥ := by
    by_contra habad
    exact hno (exists_nonabelian_large_slice_knownSimple (e := e) (hz := hz) (hn := hn) hb p habad)
  have hPV : P ≤ V d.radical (alpha d.radical) := localZSpan_le_V d.radical hca.le
  have hQaGc : Q d.radical (alpha d.radical) ≤ stabilizer d.radical c :=
    Q_le_stabilizer_of_dist_two d.radical _ _ rfl hac
  have hPQ : P ≤ Q d.radical c := by
    rw [←C_eq_Q s hc c hcCol]
    exact le_inf ((hPV.trans (V_le_Q d.radical rfl hb2)).trans hQaGc)
      ((commutator_eq_bot_iff_le_centralizer.mp hPab).trans
        (centralizer_le (Z_le_localZSpan d.radical c (alpha d.radical))))
  exact hno (initial_selection_of_eligible_trapped_small_predecessor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hslice hat hct hel hPQ)


include e hz hn in
/-- A small predecessor slice alone supplies a nonabelian large-slice path.
If the whole radius were trapped, an eligible neighboring orbit span would
be trapped as well, contradicting the normal-core argument. The resulting
radius escape constructs the reciprocal path and the forward eligibility. -/
theorem initial_selection_of_small_predecessor_knownSimple
    (hb : replacementDistance h d = 4) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hslice : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2) :
    ∃ w, ∃ r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) w,
      ⁅localZSpan d.radical (r.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (r.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (r.walk.getVert 2)) := by
  classical
  by_contra hno
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hescape : ¬ V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert 2) := by
    intro htrap
    have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
      apply (cosetGraph_adj d.radical _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using
        p.walk.adj_getVert_succ (i := 0) (by omega)
    obtain ⟨delta,hdelta,hel⟩ := exists_eligible_neighbor_at_edge s hc hb2 rfl hat
    have hdist : (cosetGraph d.radical).dist delta (alpha d.radical) ≤ 2 := by
      have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hdelta)
      have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
      have hh := (cosetGraph_connected d.radical).dist_triangle
        (u := delta) (v := p.walk.getVert 1) (w := alpha d.radical)
      omega
    exact hno (initial_selection_of_eligible_trapped_small_predecessor_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hslice hat hdelta hel
      ((localZSpan_le_V d.radical hdist).trans htrap))
  obtain ⟨w,q,hq⟩ := radius_escape_reciprocal_path s hc hb p hescape
  have hel : ¬ U d.radical (p.walk.getVert 2) ≤
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    simpa only [hq] using critical_start_not_le_second_slice s hc hb2 q
  exact hno (initial_selection_of_eligible_small_predecessor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hslice hel)


include e hz hn in
/-- The small-predecessor selection applies at every component vertex, with
the original path and its literal midpoint slice transported together. -/
theorem initial_selection_of_small_predecessor_at_knownSimple
    (hb : replacementDistance h d = 4) {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hslice : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2) :
    ∃ w, ∃ r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) w,
      ⁅localZSpan d.radical (r.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (r.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (r.walk.getVert 2)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcCol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hs : (B d.radical ((p.act g⁻¹).walk.getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (act d.radical g⁻¹ z)) ≤ 2 := by
    change (B d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex _ ≤ 2
    rw [actWalk_getVert,Escape.PairingControl.FirstPairing.B_act hb2 _ _ hcCol,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hslice
  have hex : ∃ r : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g⁻¹ a) (act d.radical g⁻¹ z),
      (B d.radical (r.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (act d.radical g⁻¹ z)) ≤ 2 := ⟨p.act g⁻¹,hs⟩
  rw [hbase] at hex
  obtain ⟨r,hr⟩ := hex
  exact initial_selection_of_small_predecessor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r hr

include e hz hn in
/-- On the literal original replacement, initial selection is established
unless both endpoint seeds have strict midpoint slices on every critical path.
The two inequalities are obtained from the same path and its reversal. -/
theorem initial_selection_or_large_midpoint_slices_knownSimple
    (hb : replacementDistance h d = 4) :
    (∃ w, ∃ r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) w,
      ⁅localZSpan d.radical (r.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (r.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (r.walk.getVert 2))) ∨
    (∀ a z, ∀ p : CriticalPath d.radical (replacementGeometry h d) a z,
      2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical a) ∧
      2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical z)) := by
  classical
  by_cases hsel : ∃ w, ∃ r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) w,
      ⁅localZSpan d.radical (r.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (r.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (r.walk.getVert 2))
  · exact Or.inl hsel
  right
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hstrict {a z : Vertex d.radical}
      (p : CriticalPath d.radical (replacementGeometry h d) a z) :
      2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical z) := by
    by_contra! hh
    exact hsel (initial_selection_of_small_predecessor_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hh)
  intro a z p
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let q : CriticalPath d.radical (replacementGeometry h d) z a := {
    start_color := p.end_color
    walk := p.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc p }
  have hmid : q.walk.getVert 2 = p.walk.getVert 2 := by
    change p.walk.reverse.getVert 2 = p.walk.getVert 2
    rw [SimpleGraph.Walk.getVert_reverse,hl]
  exact ⟨by simpa only [hmid] using hstrict q,hstrict p⟩


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

