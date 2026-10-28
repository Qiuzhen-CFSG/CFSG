module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSixteenEscape
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSpanCollapse
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSpanSelection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer

/-!
# The actual forward seed-orbit kernel without a cube-image hypothesis

In the source (5.9) small-slice configuration, suppose the forward seed orbit
were controlled by its whole-core displacement and the starting seed.
Its join with the starting seed is then locally normal. The critical
transposition controls its quotient by the core commutator; nilpotent
commutator saturation collapses the orbit to a single adjacent-seed join.
That join has index at most eight over the starting seed, so normal-section
control puts it in the Baumann slice, contradicting the retained seed escape.

Thus the elementary-actor estimate applies to the actual seed orbit joined
to the starting seed. The whole actor is elementary in the radius, lies in
the literal last edge core and has the required critical index. Its reverse
seed-kernel commutator has order two and is aligned with the critical line
and the full endpoint fixed subgroup. A conjugate seed realizes that line;
normal-section control proves that the same conjugate of the shifted normal
span has kernel displacement outside it. This last step needs no bound on
the whole predecessor core. The same whole-core noncontrol excludes the
permutation extension and proves full-X central generation. Both full-X
displacements therefore agree with the seed displacements.

The final theorem constructs these groups and both overlapping paths in the
image-sixteen branch using the proved critical escape. Both moving covers and
all central attachments are retained. The selected kernel lies in the actual
neighboring small mover, which centralizes its order-two commutator. Control
of the larger orbit span, the strict forward inequality and the terminal
large-distance exclusions remain with the source assembly.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3), (5.6) and (5.9), printed pp.866--867,917--918,920--922.
The internal imports reuse the already checked last-edge, seed-kernel and
small normal section calculations without widening their public boundaries.
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


namespace SylowForwardKernel
include s

private theorem seed_orbit_core_control_false
    (hc : DistanceTwo.CentralLayer d) (hb : 4 < replacementDistance h d)
    {c z a t : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical c) < 4)
    (ha : color d.radical a = false)
    (hct : Adjacent d.radical c t) (hat : Adjacent d.radical a t)
    (P : Subgroup (FreeAmalgam d.radical)) (hPG : P ≤ stabilizer d.radical c)
    (hgen : P ⊔ Z d.radical z = stabilizer d.radical c)
    (hZaB : ¬ Z d.radical a ≤ B d.radical c ((replacementGeometry h d).Z_normal _))
    (hcontrol : ⁅conjugateSpanBy (Z d.radical a) P,Z d.radical z⁆ ≤
      ⁅conjugateSpanBy (Z d.radical a) P,Q d.radical c⁆ ⊔ Z d.radical c) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let D := conjugateSpanBy (Z d.radical a) P
  let E := Z d.radical a ⊔ Z d.radical c
  let N := conjugateSpanBy E P
  let Qc := Q d.radical c
  have hnear : (cosetGraph d.radical).dist c a ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    have hh := (cosetGraph_connected d.radical).dist_triangle (u := c) (v := t) (w := a)
    simpa only [h₁,h₂] using hh
  have hZaV : Z d.radical a ≤ V d.radical c :=
    (Z_le_localZSpan d.radical a c).trans
      (localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm]; exact hnear))
  have hEV : E ≤ V d.radical c := sup_le hZaV (Z_le_VBall d.radical c 2)
  have hNV : N ≤ V d.radical c := conjugateSpanBy_le hEV
    (hPG.trans (DistanceEight.V_normalized d.radical c))
  have hNQ : N ≤ Qc := hNV.trans ((replacementGeometry h d).V_le_Q hb2 c q.start_color)
  have hEQ : Qc ≤ normalizer (E : Set (FreeAmalgam d.radical)) :=
    (le_inf ((Q_le_stabilizer_of_dist_le_two c a q.start_color ha hnear).trans
      (Z_normalized d.radical a))
      ((show Qc ≤ stabilizer d.radical c from fun _ hx => hx.1).trans
        (Z_normalized d.radical c))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hND : N = D ⊔ Z d.radical c := by
    apply le_antisymm
    · apply conjugateSpanBy_le (sup_le (le_conjugateSpanBy _ _ |>.trans le_sup_left) le_sup_right)
      exact (le_inf (le_normalizer_conjugateSpanBy _ _)
        (hPG.trans (Z_normalized d.radical c))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact sup_le (conjugateSpanBy_mono le_sup_left le_rfl)
        (le_sup_right.trans (le_conjugateSpanBy _ _))
  have hZG : Z d.radical z ≤ stabilizer d.radical c :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) c q.start_color (by
      rw [(replacementGeometry h d).distance_constant c q.start_color]
      exact replacementDistance_pos h d) q.critical
  have hcrit : ⁅Z d.radical c,Z d.radical z⁆ ≤ Z d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hZG.trans (Z_normalized d.radical c))
  have hDN : D ≤ N := hND.symm ▸ le_sup_left
  have hZN : Z d.radical c ≤ N := hND.symm ▸ le_sup_right
  have hKnorm : Qc ≤ normalizer (N : Set (FreeAmalgam d.radical)) :=
    TwoOrbitSpan.normalizes_span E P Qc hEQ (hPG.trans (Q_normalized d.radical c))
  have hNZ : ⁅N,Z d.radical z⁆ ≤ N := by
    conv_lhs => rw [hND]
    apply commutator_sup_le_of_relative_normal N D (Z d.radical c)
      (Z d.radical z) N N.le_normalizer hDN hZN
    · exact hcontrol.trans (sup_le
        ((commutator_mono hDN le_rfl).trans
          (le_normalizer_iff_commutator_le_left.mp hKnorm)) hZN)
    · exact hcrit.trans hZN
  have hNnorm : stabilizer d.radical c ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    exact sup_le (le_normalizer_conjugateSpanBy _ _)
      (le_normalizer_iff_commutator_le_left.mpr hNZ)
  let M := ⁅N,Qc⁆ ⊔ Z d.radical c
  have hMnorm : stabilizer d.radical c ≤ normalizer (M : Set (FreeAmalgam d.radical)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    dsimp only [M]
    rw [Subgroup.map_sup,map_commutator,mem_normalizer_iff_map_conj_eq.mp (hNnorm hg),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical c hg),
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical c hg)]
  have hNcontrol : ⁅N,Z d.radical z⁆ ≤ M := by
    conv_lhs => rw [hND]
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical c)
      D (Z d.radical c) (Z d.radical z) M hMnorm
      ((hDN.trans hNQ).trans (fun _ hx => hx.1)) (Z_le_stabilizer d.radical c)
    · have hDK : ⁅D,Qc⁆ ≤ ⁅N,Qc⁆ := commutator_mono hDN le_rfl
      exact hcontrol.trans (sup_le_sup_right hDK (Z d.radical c))
    · exact hcrit.trans le_sup_right
  have hfull : ⁅N,stabilizer d.radical c⁆ ≤ M :=
    small_critical_section_control s hc q hsmall N M
      (hNQ.trans (fun _ hx => hx.1)) hNnorm hMnorm le_sup_left hNcontrol
  let := finite_stabilizer d.radical c
  let : Finite Qc := Finite.of_injective
    (inclusion (show Qc ≤ stabilizer d.radical c from fun _ hx => hx.1))
      (inclusion_injective _)
  have hcollapse : N = E := conjugateSpanBy_eq_of_nilpotent_commutator_bound
    E P Qc (Z d.radical c)
    (Q_isPGroup d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d) c q.start_color).isNilpotent
    hNQ hEQ le_sup_right ((commutator_mono le_rfl hPG).trans hfull)
  have hindex : (Z d.radical c).relIndex N ≤ 8 := by
    rw [hcollapse]
    exact SylowSpanSelection.adjacent_seed_span_index_le_eight
      (e := e) (hz := hz) (hn := hn) hb q.start_color hct hat
  exact hZaB ((le_sup_left.trans (le_conjugateSpanBy E P)).trans
    (SylowSpanSelection.normal_small_radius_le_slice_at s hb2 q.start_color
      N hNV hNnorm hindex))

/-- The actual elementary seed orbit has an aligned order-two reverse-kernel
commutator, without a condition on the replacement's radical image. -/
theorem generated_seed_orbit_kernel_line
    (hc : DistanceTwo.CentralLayer d) (hb : 4 < replacementDistance h d)
    {c z a t : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical c) < 4)
    (ha : color d.radical a = false)
    (hct : Adjacent d.radical c t) (hat : Adjacent d.radical a t)
    (P : Subgroup (FreeAmalgam d.radical)) (hPG : P ≤ stabilizer d.radical c)
    (hgen : P ⊔ Z d.radical z = stabilizer d.radical c)
    (hZaB : ¬ Z d.radical a ≤ B d.radical c ((replacementGeometry h d).Z_normal _))
    (hDpre : conjugateSpanBy (Z d.radical a) P ≤
      Q d.radical (q.walk.getVert (q.walk.length-2))) :
    let D := conjugateSpanBy (Z d.radical a) P
    let K := Z d.radical z ⊓ Q d.radical c
    Nat.card (⁅D,K⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅D,K⁆ ≤ ⁅Z d.radical c,Z d.radical z⁆ ⊔
        (Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
      ¬ ⁅D,Z d.radical z⁆ ≤ ⁅D,K⁆ ⊔ ⁅Z d.radical c,Z d.radical z⁆ := by
  let D := conjugateSpanBy (Z d.radical a) P
  let K := Z d.radical z ⊓ Q d.radical c
  let N := D ⊔ Z d.radical c
  have hb2 : 2 < replacementDistance h d := by omega
  have hlast := critical_last_edge_inputs (h := h) hb2 q
  have hfixed := critical_full_kernel_eq s hc q
  have hZaV := neighbor_seed_le_radius hct hat
  have hDV : D ≤ V d.radical c := conjugateSpanBy_le hZaV
    (hPG.trans (DistanceEight.V_normalized d.radical c))
  have hNV : N ≤ V d.radical c := sup_le hDV (Z_le_VBall d.radical c 2)
  have hNC : Z d.radical c ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c q.start_color)).trans
      (centralizer_le (hDV.trans ((replacementGeometry h d).V_le_Q hb2 c q.start_color)))
  have hZK : Z d.radical c ≤ centralizer (K : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c q.start_color)).trans
      (centralizer_le inf_le_right)
  have hNK : ⁅N,K⁆ = ⁅D,K⁆ := commutator_sup_fixed D (Z d.radical c) K
    (hNC.trans (Subgroup.centralizer_le_normalizer _)) hZK
  have hnot : ¬ ⁅D,Z d.radical z⁆ ≤ ⁅D,K⁆ ⊔ ⁅Z d.radical c,Z d.radical z⁆ :=
    fun hh => seed_orbit_core_control_false s hc hb q hsmall ha hct hat P hPG hgen hZaB
      (hh.trans (sup_le_sup (commutator_mono le_rfl inf_le_right)
        (((critical_Z_commutator_le_moving (h := h) q).trans inf_le_left).trans
          (DistanceEight.U_le_Z d.radical c))))
  have hfail : ¬ ⁅Z d.radical z,N⁆ ≤
      ⁅Z d.radical z ⊓ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)),N⁆ ⊔
        ⁅Z d.radical z,Z d.radical c⁆ := by
    intro hh
    rw [←hfixed,commutator_comm K N,hNK,commutator_comm (Z d.radical z) (Z d.radical c)] at hh
    apply hnot
    rw [commutator_comm (Z d.radical z) N] at hh
    exact (commutator_mono le_sup_left le_rfl).trans hh
  let := V_elementary_of_four_lt d.radical q.start_color hb
  have hel : IsElementaryAbelian 2 N := IsElementaryAbelian.of_le hNV
  have hindex : (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ 2 := by
    let := finite_Z d.radical z
    let : Finite (U d.radical z) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
    have hQC : Q d.radical c ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical c q.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc q hsmall).2
  have hline := elementary_edge_kernel_small_aligned s hc q.end_color hlast.1
    (Z d.radical c) N hlast.2.2 (sup_le (hDpre.trans hlast.2.1) hlast.2.2)
    le_sup_right hel q.critical.2 hindex hfail
  rw [←hfixed,commutator_comm K N,hNK] at hline
  have hDG : D ≤ stabilizer d.radical z :=
    (hDpre.trans hlast.2.1).trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hlast.1))
  have hJZ : ⁅D,K⁆ ≤ Z d.radical z := (commutator_mono le_rfl inf_le_left).trans
    (le_normalizer_iff_commutator_le_right.mp (hDG.trans (Z_normalized d.radical z)))
  let := finite_Z d.radical z
  let : Finite (⁅D,K⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hJZ) (inclusion_injective _)
  have hJne : ⁅D,K⁆ ≠ ⊥ := by
    intro he
    have hcomm := small_critical_predecessor_commutator s hc hb2 q hsmall D hDpre
      (commutator_eq_bot_iff_le_centralizer.mp he)
    exact span_control_false s hb2 q.start_color D P (Z d.radical z) hDV hPG
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) c q.start_color (by
        rw [(replacementGeometry h d).distance_constant c q.start_color]
        exact replacementDistance_pos h d) q.critical)
      (critical_reverse_pair s hc q).2 (le_normalizer_conjugateSpanBy _ _) hgen
      (fun hh => hZaB ((le_conjugateSpanBy _ _).trans hh)) hcomm
  have hpos := (one_lt_card_iff_ne_bot ⁅D,K⁆).mpr hJne
  have hcard : Nat.card (⁅D,K⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 := hline.1
  change Nat.card (⁅D,K⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧ _
  refine ⟨by omega,?_,hnot⟩
  simpa only [commutator_comm (Z d.radical z) (Z d.radical c)] using hline.2

/-- The noncontrol of the actual adjacent-seed orbit excludes the full
permutation extension and identifies its full-X kernel with the seed kernel. -/
theorem generated_seed_orbit_full_kernel
    (hc : DistanceTwo.CentralLayer d) (hb : 4 < replacementDistance h d)
    {c z a t : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical c) < 4)
    (ha : color d.radical a = false)
    (hct : Adjacent d.radical c t) (hat : Adjacent d.radical a t)
    (P : Subgroup (FreeAmalgam d.radical)) (hPG : P ≤ stabilizer d.radical c)
    (hgen : P ⊔ Z d.radical z = stabilizer d.radical c)
    (hZaB : ¬ Z d.radical a ≤ B d.radical c ((replacementGeometry h d).Z_normal _))
    (hDpre : conjugateSpanBy (Z d.radical a) P ≤
      Q d.radical (q.walk.getVert (q.walk.length-2))) :
    let D := conjugateSpanBy (Z d.radical a) P
    X d.radical z = U d.radical z ⊔
      (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
    (X d.radical z ⊓ Q d.radical c) = (Z d.radical z ⊓ Q d.radical c) ⊔
      (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
    ⁅D,X d.radical z⁆ = ⁅D,Z d.radical z⁆ ∧
    ⁅D,X d.radical z ⊓ Q d.radical c⁆ = ⁅D,Z d.radical z ⊓ Q d.radical c⁆ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let D := conjugateSpanBy (Z d.radical a) P
  have hDV : D ≤ V d.radical c := conjugateSpanBy_le (neighbor_seed_le_radius hct hat)
    (hPG.trans (DistanceEight.V_normalized d.radical c))
  have hDQ : D ≤ Q d.radical c := hDV.trans ((replacementGeometry h d).V_le_Q hb2 c q.start_color)
  have hedge := critical_last_edge_inputs (h := h) hb2 q
  have hDz : D ≤ stabilizer d.radical z :=
    (hDpre.trans hedge.2.1).trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hedge.1))
  let rev : CriticalPath d.radical (replacementGeometry h d) z c :=
    CriticalPath.ofPair q.end_color (critical_reverse_pair s hc q)
  have hs : (Q d.radical c).relIndex (Z d.radical z) < 4 := by
    rw [(small_critical_indices s hc q hsmall).2]
    decide
  have hXgen : X d.radical z = U d.radical z ⊔
      (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
    rcases full_X_generation_or_control_at s hc rev hs with hgenX | hcontrol
    · exact hgenX
    exfalso
    have hZX (v : Vertex d.radical) (hv : color d.radical v = false) :
        Z d.radical v ≤ X d.radical v := by
      apply (replacementGeometry h d).omega_bound v hv
      rw [(replacementGeometry h d).distance_constant v hv]
      exact replacementDistance_pos h d
    have hXG : X d.radical z ≤ stabilizer d.radical c :=
      CriticalCriterion.critical_X_le_stabilizer d.radical (replacementGeometry h d)
        (edgeCentralizerCondition s hc) (replacementDistance_pos h d) z q.end_color c
        (critical_reverse_pair s hc q)
    have hRZ : ⁅X d.radical z,Z d.radical c⁆ ≤ Z d.radical c :=
      le_normalizer_iff_commutator_le_right.mp (hXG.trans (Z_normalized d.radical c))
    have hDR : D ≤ centralizer ((⁅X d.radical z,Z d.radical c⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) :=
      (hDQ.trans (Q_le_centralizer_X d.radical c)).trans
        (centralizer_le (hRZ.trans (hZX c q.start_color)))
    apply seed_orbit_core_control_false s hc hb q hsmall ha hct hat P hPG hgen hZaB
    exact (commutator_mono le_rfl (hZX z q.end_color)).trans
      ((hcontrol D hDz hDR).trans (sup_le (hRZ.trans le_sup_right)
        ((commutator_mono le_rfl inf_le_right).trans le_sup_left)))
  exact ⟨hXgen,critical_X_kernel_of_central_generation s hc q hXgen,
    critical_X_displacements_of_central_generation s hc q hXgen D hDz⟩

/-- An actual order-two full-seed commutator fixes the neighboring maximum
small mover, and its actor lies in that mover. -/
theorem seed_kernel_line_small_mover
    (hc : DistanceTwo.CentralLayer d) (hb : 4 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (A : Subgroup (FreeAmalgam d.radical)) (hAt : A ≤ Q d.radical t)
    (hcard : Nat.card (⁅Z d.radical a,A⁆ : Subgroup (FreeAmalgam d.radical)) = 2) :
    let T := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
    let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
    A ≤ J ∧ J ≤ centralizer
      ((⁅Z d.radical a,A⁆ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let T := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
  let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
  have hAG : A ≤ stabilizer d.radical a :=
    hAt.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  have hRZ : ⁅Z d.radical a,A⁆ ≤ Z d.radical a :=
    le_normalizer_iff_commutator_le_left.mp (hAG.trans (Z_normalized d.radical a))
  let := finite_Z d.radical a
  let : Finite (⁅Z d.radical a,A⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hRZ) (inclusion_injective _)
  have hUcard : Nat.card (⁅U d.radical a,A⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 :=
    (card_le_of_le (commutator_mono (DistanceEight.U_le_Z d.radical a) le_rfl)).trans_eq hcard
  have hindex := moving_small_commutator_fixed_index s hc ha A hAG hUcard
  obtain ⟨J₀,_,hJ₀,_,hJT,_,_,_,hact⟩ :=
    SylowSmallMovers.edge_normalizer_small_movers_knownSimple
      (e := e) (hz := hz) (hn := hn) hb ha hat
  change J = J₀ at hJ₀
  rw [←hJ₀] at hJT hact
  have hsmall := hact A hAt hindex
  have hcomm : ⁅J,A⁆ ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    hsmall.2.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a ha)))
  have hJN : J ≤ normalizer
      ((⁅Z d.radical a,A⁆ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    rw [commutator_comm (Z d.radical a)]
    exact SylowNormalizer.fixed_mod_central_normalizes A (Z d.radical a) J
      (hAG.trans (Z_normalized d.radical a))
      ((hJT.trans inf_le_right).trans (Z_normalized d.radical a)) hcomm
  exact ⟨hsmall.1,hJN.trans (normalizer_le_centralizer_of_card_two _ hcard)⟩

private theorem conjugate_seed_kernel_mover
    (hc : DistanceTwo.CentralLayer d) (hb : 4 < replacementDistance h d)
    (himage : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {c a t : Vertex d.radical} (hc0 : color d.radical c = false) (ha : color d.radical a = false)
    (hct : Adjacent d.radical c t) (hat : Adjacent d.radical a t)
    (K : Subgroup (FreeAmalgam d.radical)) (hKQ : K ≤ Q d.radical c)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical c)
    (hcard : Nat.card (⁅(Z d.radical a).map (MulAut.conj x).toMonoidHom,K⁆ :
      Subgroup (FreeAmalgam d.radical)) = 2) :
    ∃ t', Adjacent d.radical c t' ∧ Adjacent d.radical (act d.radical x⁻¹ a) t' ∧
      let J := SmallMover.join (U d.radical (act d.radical x⁻¹ a))
        (Q d.radical (act d.radical x⁻¹ a)) (Q d.radical t') 4
      K ≤ J ∧ J ≤ centralizer ((⁅(Z d.radical a).map (MulAut.conj x).toMonoidHom,K⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let ax := act d.radical x⁻¹ a
  let tx := act d.radical x⁻¹ t
  have hctx : Adjacent d.radical c tx := by
    have hh := (adjacent_act_iff d.radical x⁻¹ c t).mpr hct
    rwa [show act d.radical x⁻¹ c = c from (stabilizer d.radical c).inv_mem hx] at hh
  have hatx : Adjacent d.radical ax tx := (adjacent_act_iff d.radical x⁻¹ _ _).mpr hat
  have haxcol : color d.radical ax = false := by rw [action_preserves_color]; exact ha
  have htxcol : color d.radical tx = true := by
    have hh := adjacent_color_ne d.radical hctx
    rw [hc0] at hh
    cases he : color d.radical tx with
    | false => exact False.elim (hh he.symm)
    | true => rfl
  have hKtx : K ≤ Q d.radical tx := hKQ.trans (Q_le_adjacent_h d.radical htxcol hctx)
  have hax : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical ax := by
    change _ = Z d.radical (act d.radical x⁻¹ a)
    rw [Z_act,inv_inv]
  have haxcard : Nat.card (⁅Z d.radical ax,K⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
    rw [←hax]
    exact hcard
  have hJfix := seed_kernel_line_small_mover s hc hb haxcol hatx K hKtx haxcard
  dsimp only at hJfix
  rw [SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d)
    himage haxcol hatx,←hax] at hJfix
  exact ⟨tx,hctx,hatx,hJfix⟩

/-- A nonzero conjugate seed-kernel commutator cannot contain the displacement
of an escaping normal radius section. No cube or predecessor-card bound is used. -/
theorem predecessor_kernel_displacement_escape
    (hb : 2 < replacementDistance h d) {c z a : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (ha : color d.radical a = false) (hca : (cosetGraph d.radical).dist c a ≤ 2)
    (Y : Subgroup (FreeAmalgam d.radical)) (hYV : Y ≤ V d.radical a)
    (hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hYB : ¬ Y ≤ B d.radical a ((replacementGeometry h d).Z_normal _))
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical c)
    (hne : ⁅(Z d.radical a).map (MulAut.conj x).toMonoidHom,
      Z d.radical z ⊓ Q d.radical c⁆ ≠ ⊥) :
    ¬ ⁅Y.map (MulAut.conj x).toMonoidHom,Z d.radical z ⊓ Q d.radical c⁆ ≤
      ⁅(Z d.radical a).map (MulAut.conj x).toMonoidHom,Z d.radical z ⊓ Q d.radical c⁆ := by
  let K := Z d.radical z ⊓ Q d.radical c
  let f := (MulAut.conj x).toMonoidHom
  let fi := (MulAut.conj x⁻¹).toMonoidHom
  let A := K.map fi
  have hAf : A.map f = K := by
    rw [map_map]
    have he : f.comp fi = MonoidHom.id (FreeAmalgam d.radical) := by
      apply MonoidHom.ext
      intro v
      change x*(x⁻¹*v*(x⁻¹)⁻¹)*x⁻¹ = v
      group
    rw [he,map_id]
  have hAQ : A ≤ Q d.radical c :=
    (map_mono (show K ≤ Q d.radical c from inf_le_right)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp
        ((Q_normalized d.radical c) ((stabilizer d.radical c).inv_mem hx)))
  have hAG : A ≤ stabilizer d.radical a := hAQ.trans
    (Q_le_stabilizer_of_dist_le_two c a q.start_color ha hca)
  have hZA : ⁅Z d.radical a,A⁆ ≤ Z d.radical a :=
    le_normalizer_iff_commutator_le_left.mp (hAG.trans (Z_normalized d.radical a))
  have hZAmap : (⁅Z d.radical a,A⁆ : Subgroup (FreeAmalgam d.radical)).map f =
      ⁅(Z d.radical a).map f,K⁆ := by rw [map_commutator,hAf]
  have hnA : ¬ A ≤ Q d.radical a := by
    intro hAcore
    have hzero : ⁅Z d.radical a,A⁆ = ⊥ := le_bot_iff.mp
      ((commutator_mono le_rfl hAcore).trans_eq (Z_centralizes_Q d.radical a ha))
    apply hne
    rw [←hZAmap,hzero,Subgroup.map_bot]
  intro hle
  have hYA : ⁅Y,A⁆ ≤ Z d.radical a := by
    apply le_trans _ hZA
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj x).injective).mp
    rwa [hZAmap,map_commutator,hAf]
  exact hYB (normalized_radius_le_slice_of_actor_at s hb ha Y A hYV hYN hAG hnA hYA)

private theorem shifted_seed_escape (hc : DistanceTwo.CentralLayer d)
    (hb : 4 < replacementDistance h d) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical (p.walk.getVert 2)) :
    Z d.radical (act d.radical y⁻¹ (alpha d.radical)) ≤ V d.radical (p.walk.getVert 2) ∧
      ¬ Z d.radical (act d.radical y⁻¹ (alpha d.radical)) ≤
        B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hcol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega : 2 ≤ p.walk.length)).mpr (by decide)
  constructor
  · have hZV : Z d.radical (alpha d.radical) ≤ V d.radical (p.walk.getVert 2) :=
      le_iSup_of_le (alpha d.radical) (le_iSup_of_le
        (show (cosetGraph d.radical).dist (alpha d.radical) (p.walk.getVert 2) ≤ 2 from
          (p.dist_start (by omega)).le) le_rfl)
    rw [Z_act,inv_inv]
    exact (map_mono hZV).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (DistanceEight.V_normalized d.radical _ hy))
  · have hBm := mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized hb2 _ hcol hy)
    intro he
    rw [Z_act,inv_inv,←hBm] at he
    exact critical_start_not_le_second_slice s hc hb2 p
      ((DistanceEight.U_le_Z d.radical _).trans
        ((map_le_map_iff_of_injective (MulAut.conj y).injective).mp he))

omit s in
/-- The literal image-sixteen small-slice configuration has a selected
order-two full-X kernel line and a shifted normal span whose kernel displacement
escapes that line. The same selected seed puts the kernel in the actual neighboring
small mover, which fixes the line. Both paths and central attachments are retained. -/
theorem sixteen_small_shifted_kernel_escape_knownSimple
    (hb : 4 < replacementDistance h d)
    (himage : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    let c := p.walk.getVert 2
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical c,T⁆
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) c z,
      (cosetGraph d.radical).dist a' z = 2 ∧
      (∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) ∧
      q.walk.getVert (q.walk.length-2) = a' ∧
      (Q d.radical z).relIndex (Z d.radical c) = 2 ∧
      ∃ y ∈ Ltilde d.radical c,
        let a := act d.radical y⁻¹ (alpha d.radical)
        let T₂ := T.map (MulAut.conj y).toMonoidHom
        let H₂ := H.map (MulAut.conj y).toMonoidHom
        let Y := (localZSpan d.radical c (alpha d.radical)).map (MulAut.conj y).toMonoidHom
        let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
        let D := conjugateSpanBy (Z d.radical a) P
        let K := Z d.radical z ⊓ Q d.radical c
        P ⊔ Z d.radical z = stabilizer d.radical c ∧
        ¬ H₂ ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) ∧
        T₂ = Q d.radical a ⊓ centralizer
          (U d.radical c ⊓ B d.radical a ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical)) ∧
        Z d.radical c ≤ Y ∧ Y ≤ V d.radical a ∧
        stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) ∧
        ¬ Y ≤ B d.radical a ((replacementGeometry h d).Z_normal _) ∧
        H₂ ≤ Z d.radical a ∧ Nat.card H₂ = 2 ∧
        H₂ ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
        ⁅Y,T₂⁆ ≤ H₂ ∧ Z d.radical a ≤ Q d.radical a' ∧ Y ≤ Q d.radical a' ∧
        D ≤ Q d.radical a' ∧ conjugateSpanBy Y P ≤ Q d.radical a' ∧
        Z d.radical a ≤ V d.radical c ∧
        ¬ Z d.radical a ≤ B d.radical c ((replacementGeometry h d).Z_normal _) ∧
        ∃ t, Adjacent d.radical c t ∧ Adjacent d.radical a t ∧
        X d.radical z = U d.radical z ⊔
          (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
        ⁅D,X d.radical z ⊓ Q d.radical c⁆ = ⁅D,K⁆ ∧
        ⁅D,X d.radical z⁆ = ⁅D,Z d.radical z⁆ ∧
        Nat.card (⁅D,K⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
        ⁅D,K⁆ ≤ ⁅Z d.radical c,Z d.radical z⁆ ⊔
          (Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
        ¬ ⁅D,Z d.radical z⁆ ≤ ⁅D,K⁆ ⊔ ⁅Z d.radical c,Z d.radical z⁆ ∧
        ∃ x ∈ P,
          ⁅(Z d.radical a).map (MulAut.conj x).toMonoidHom,K⁆ = ⁅D,K⁆ ∧
          ¬ ⁅Y.map (MulAut.conj x).toMonoidHom,K⁆ ≤ ⁅D,K⁆ ∧
          ¬ ⁅conjugateSpanBy Y P,K⁆ ≤ ⁅D,K⁆ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hesc := sixteen_criticalEscape_knownSimple
    (e := e) (hz := hz) (hn := hn) hb himage
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
  let D := conjugateSpanBy (Z d.radical a) P
  let K := Z d.radical z ⊓ Q d.radical c
  have hyG : y ∈ stabilizer d.radical c := Ltilde_le_stabilizer c hy
  have ha : color d.radical a = false := by rw [action_preserves_color]; rfl
  have hca : (cosetGraph d.radical).dist c a = 2 := by
    have hfix : act d.radical y⁻¹ c = c := (stabilizer d.radical c).inv_mem hyG
    have hh := dist_act d.radical y⁻¹ c (alpha d.radical)
    rw [hfix,SimpleGraph.dist_comm (u := c) (v := alpha d.radical)] at hh
    exact hh.trans (p.dist_start (by omega))
  obtain ⟨hZaV,hZaB⟩ := shifted_seed_escape s hc hb p y hyG
  have hDpre : D ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
    rw [hpre]
    exact hDQ
  let tx := act d.radical y⁻¹ t
  have hctx : Adjacent d.radical c tx := by
    have hh := (adjacent_act_iff d.radical y⁻¹ c t).mpr hct
    rwa [show act d.radical y⁻¹ c = c from (stabilizer d.radical c).inv_mem hyG] at hh
  have hatx : Adjacent d.radical a tx := (adjacent_act_iff d.radical y⁻¹ _ _).mpr hat
  have hfull := generated_seed_orbit_full_kernel s hc hb q hqsmall
    ha hctx hatx P inf_le_left hgen hZaB hDpre
  obtain ⟨hJcard,hJalign,hJnot⟩ := generated_seed_orbit_kernel_line s hc hb q hqsmall
    ha hctx hatx P inf_le_left hgen hZaB hDpre
  obtain ⟨x,hx⟩ := exists_span_line_generator (Z d.radical a) P K hJcard
  have hne : ⁅(Z d.radical a).map (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom,K⁆ ≠ ⊥ := by
    intro hh
    rw [←hx,hh,card_bot] at hJcard
    omega
  have hYnot := predecessor_kernel_displacement_escape s hb2 q ha hca.le
    Y hYV hYN hYB x x.property.1 hne
  rw [hx] at hYnot
  have hYxW : Y.map (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom ≤
      conjugateSpanBy Y P := by
    rw [conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : P => Y.map (MulAut.conj (k : FreeAmalgam d.radical)).toMonoidHom) x
  have hHcardExact : Nat.card H₂ = 2 := by
    rw [card_map_of_injective (MulAut.conj y).injective]
    exact hline.2.1
  exact ⟨z,q,hd,hover,hpre,hi,y,hy,hgen,hmove,hT,hZcY,hYV,hYN,hYB,hHZa,hHcardExact,hHCa,
    hcomm,hZaQ,hYQ,hDQ,hWQ,hZaV,hZaB,tx,hctx,hatx,hfull.1,hfull.2.2.2,hfull.2.2.1,hJcard,hJalign,hJnot,
    x,x.property,hx,hYnot,(fun hh => hYnot ((commutator_mono hYxW le_rfl).trans hh))⟩

omit s in
/-- The selected source (5.9) line is fixed by the literal neighboring small
mover containing the whole reverse kernel. The seed realization and shifted
normal-section escape are retained. -/
theorem sixteen_small_shifted_kernel_mover_knownSimple
    (hb : 4 < replacementDistance h d)
    (himage : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    let c := p.walk.getVert 2
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) c z,
      q.walk.getVert (q.walk.length-2) = a' ∧
      (Q d.radical z).relIndex (Z d.radical c) = 2 ∧
      ∃ a t, Adjacent d.radical c t ∧ Adjacent d.radical a t ∧
        let K := Z d.radical z ⊓ Q d.radical c
        let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
        Nat.card (⁅Z d.radical a,K⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
        K ≤ J ∧ J ≤ centralizer ((⁅Z d.radical a,K⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        ∃ Y : Subgroup (FreeAmalgam d.radical),
          Y ≤ Q d.radical a' ∧ ¬ ⁅Y,K⁆ ≤ ⁅Z d.radical a,K⁆ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨z,q,_,_,hpre,hi,y,hy,hgen,hmove,hT,hZcY,hYV,hYN,hYB,hHZa,hHcard,hHCa,
    hcomm,hZaQ,hYQ,hDQ,hWQ,hZaV,hZaB,t,hct,hat,hfull,hKfull,hXfull,hJcard,hJalign,hJnot,
    x,hx,hxeq,hYnot,hWnot⟩ :=
    sixteen_small_shifted_kernel_escape_knownSimple (e := e) (hz := hz) (hn := hn)
      hb himage p hsmall hslice
  let c := p.walk.getVert 2
  let a := act d.radical y⁻¹ (alpha d.radical)
  let K := Z d.radical z ⊓ Q d.radical c
  let Y := (localZSpan d.radical c (alpha d.radical)).map (MulAut.conj y).toMonoidHom
  let P := stabilizer d.radical c ⊓ centralizer
    ((⁅U d.radical c,Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) : Set _)⁆ :
        Subgroup (FreeAmalgam d.radical)).map (MulAut.conj y).toMonoidHom : Set _)
  have ha : color d.radical a = false := by rw [action_preserves_color]; rfl
  have hselectedCard : Nat.card (⁅(Z d.radical a).map (MulAut.conj x).toMonoidHom,K⁆ :
      Subgroup (FreeAmalgam d.radical)) = 2 := by rw [hxeq]; exact hJcard
  obtain ⟨t',hct',hat',hKJ,hJR⟩ := conjugate_seed_kernel_mover s hc hb himage q.start_color
    ha hct hat K inf_le_right x hx.1 hselectedCard
  have hax : (Z d.radical a).map (MulAut.conj x).toMonoidHom =
      Z d.radical (act d.radical x⁻¹ a) := by
    conv_rhs => rw [Z_act,inv_inv]
  have hYxW : Y.map (MulAut.conj x).toMonoidHom ≤ conjugateSpanBy Y P := by
    rw [conjugateSpanBy_eq_iSup_conj]
    exact le_iSup_of_le (⟨x,hx⟩ : P) le_rfl
  refine ⟨z,q,hpre,hi,act d.radical x⁻¹ a,t',hct',hat',?_,hKJ,?_,
    Y.map (MulAut.conj x).toMonoidHom,hYxW.trans hWQ,?_⟩
  · rwa [←hax]
  · rwa [←hax]
  · rwa [←hax,hxeq]

end SylowForwardKernel
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
