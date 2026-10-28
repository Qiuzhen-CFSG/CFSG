module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.FullCoverMovement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightInitialSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ResidualSmallSection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.FullCoverMovement
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.NonnormalSelection

/-!
# The full backward kernel under an order-eight selector

For a small critical path c--t--a--u--z, let K = Z_c intersect Q_z and
J = K joined with Z_a. Suppose an actor W fixes the critical commutator,
normalizes J, and generates G_a together with Q_t. A strict Baumann slice
of U_c is impossible. Indeed, if Q_t fixed the critical commutator then it
would normalize K. The section J/Z_a has order at most eight, so residual
invariance would put J in the Baumann subgroup, contradicting strictness.
Otherwise the full-cover orbit calculation gives
[Z_c,Q_a] = [Z_c,Z_z] joined with [K,Q_a], of order at most eight.
This movement is invariant under both generators of G_a. The symmetric-six
small-section theorem makes it residual-fixed; its omega-center placement
then makes the critical commutator central, giving the same contradiction.

The actual application uses the completed EightEqual, EightUnequal and
EightBaumann selection through EightInitialSelection. The original endpoint
seed fixes the backward critical commutator by its literal midpoint-core
placement. Thus the selected backward critical image is large, or that
endpoint seed fails to normalize the full kernel join. Both covers, central
attachments and the original replacement data are retained. Constructing
compatible source-(5.12)(1) normality, excluding large critical images, and
assembling DistanceFourInput remain separate source obligations.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), (5.7) and (5.12)(1)--(3), printed pp.866--867,919,924--927.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.GroupTheory Representation.NormalElementaryQuotient
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- Normality of the full kernel join suffices; no commutator bound for
the actor on that join is needed. -/
private theorem strict_small_normalized_actor_false
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {c z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) c z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical c) < 4)
    (W : Subgroup (FreeAmalgam d.radical))
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ W = stabilizer d.radical (p.walk.getVert 2))
    (hstrict : 2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c))
    (hWN : W ≤ normalizer (((Z d.radical c ⊓ Q d.radical z) ⊔
      Z d.radical (p.walk.getVert 2) : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hWfix : ⁅Z d.radical c,Z d.radical z⁆ ≤ centralizer (W : Set (FreeAmalgam d.radical))) : False := by
  let a := p.walk.getVert 2
  let t := p.walk.getVert 1
  let K := Z d.radical c ⊓ Q d.radical z
  let D := ⁅Z d.radical c,Z d.radical z⁆
  let H := ⁅Z d.radical c,Q d.radical a⁆
  let F := ⁅K,Q d.radical a⁆
  let J := K ⊔ Z d.radical a
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have ha : color d.radical a = false := (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hTGc : Q d.radical t ≤ stabilizer d.radical c := fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have hTGa : Q d.radical t ≤ stabilizer d.radical a := fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hWG : W ≤ stabilizer d.radical a := le_sup_right.trans_eq hgen
  have hZcQ : Z d.radical c ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c p.start_color)
    rw [(replacementGeometry h d).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact hb2
  have hZwQ : Z d.radical z ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact hb2
  have hKV : K ≤ V d.radical a := inf_le_left.trans
    (le_iSup_of_le c (le_iSup_of_le (by rw [p.dist_start (by omega)]) le_rfl))
  have central_false (hcentral : D ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) : False := by
    have hTK : Q d.radical t ≤ normalizer (K : Set (FreeAmalgam d.radical)) := by
      have hh := le_inf hTGc (le_centralizer_iff.mp (hcentral.trans (centralizer_le hTGa)))
      rw [←small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall] at hh
      exact hh.trans inf_le_right
    have hTJ : Q d.radical t ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
      (le_inf hTK (hTGa.trans (Z_normalized d.radical a))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    have hGJ : stabilizer d.radical a ≤ normalizer (J : Set (FreeAmalgam d.radical)) := by
      rw [←hgen]
      exact sup_le hTJ hWN
    have hJV : J ≤ V d.radical a := sup_le hKV (Z_le_VBall d.radical _ 2)
    let := finite_stabilizer d.radical a
    let : Finite J := Finite.of_injective
      (inclusion (hJV.trans ((V_le_Q d.radical ha hb2).trans (fun _ hx => hx.1))))
      (inclusion_injective _)
    let : Finite (Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :=
      Finite.of_injective (inclusion (sup_le
        (hZcQ.trans (fun _ hx => hx.1)) (Z_le_stabilizer d.radical a)))
        (inclusion_injective _)
    have hJindex : (Z d.radical a).relIndex J ≤ 8 :=
      (relIndex_le_of_le_right (show J ≤ Z d.radical c ⊔ Z d.radical a from
        sup_le_sup inf_le_left le_rfl) index_ne_zero_of_finite).trans
          (DistanceFour.adjacent_seed_span_index_le_eight
            (e := e) (hz := hz) (hn := hn) hb2 ha hat hct)
    have hJB := residual_small_radius_le_slice_knownSimple (e := e) hb2 ha J hJV
      ((Ltilde_le_stabilizer a).trans hGJ) hJindex
    let := finite_Z d.radical c
    have hi := relIndex_le_of_le_left (le_sup_left.trans hJB : K ≤ B d.radical a _)
      (index_ne_zero_of_finite (H := K.subgroupOf (Z d.radical c)))
    change (B d.radical a _).relIndex (Z d.radical c) ≤
      (Z d.radical c ⊓ Q d.radical z).relIndex (Z d.radical c) at hi
    rw [inf_relIndex_left,(small_critical_indices s hc p hsmall).1] at hi
    have hsmallSlice := (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical c)
      index_ne_zero_of_finite).trans hi
    exact (not_le_of_gt hstrict) hsmallSlice
  have hmove : ¬ Q d.radical t ≤ centralizer (D : Set (FreeAmalgam d.radical)) := by
    intro hh
    apply central_false
    apply le_centralizer_iff.mp
    rw [←hgen]
    exact sup_le hh (le_centralizer_iff.mp hWfix)
  have hQt : IsPGroup 2 (Q d.radical t) := by
    obtain ⟨i,_,_,hiR,_,_⟩ := SylowAdjacent.edge_coordinates (h := h) hc p.start_color hct
    rw [←hiR]
    exact (replacement_radical_isPGroup h d).map i
  have hPQ : Q d.radical a ≤ Q d.radical t := Q_le_adjacent_h d.radical ht hat
  have hDX : D ≤ X d.radical a := by
    have hVc : Z d.radical c ≤ V d.radical a :=
      le_iSup_of_le c (le_iSup_of_le (by rw [p.dist_start (by omega)]) le_rfl)
    have hVz : Z d.radical z ≤ V d.radical a :=
      le_iSup_of_le z (le_iSup_of_le (by rw [SimpleGraph.dist_comm,p.dist_end,hl]) le_rfl)
    exact (commutator_mono hVc hVz).trans (radius_bounds_general s hc hb2 ha c z).2.1
  have hfix : Q d.radical a ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (hDX.trans (fun _ hx => (mem_omegaCenter_iff.mp hx).2.2))
  obtain ⟨hdecomp,hquad,hcard⟩ := small_orbit_movement s hc p hsmall
    (Q d.radical t) (Q d.radical a) hTGc hQt le_rfl hPQ
    (hTGa.trans (Q_normalized d.radical a)) hZwQ hfix hmove
  have hHU : H ≤ U d.radical c := by
    change ⁅Z d.radical c,Q d.radical a⁆ ≤ U d.radical c
    rw [seed_commutator_eq_moving (h := h) (e := e) (hz := hz) p.start_color hct _ hPQ]
    exact le_normalizer_iff_commutator_le_left.mp ((hPQ.trans hTGc).trans (U_normalized c))
  have hHQ : H ≤ Q d.radical a := (hHU.trans (DistanceEight.U_le_Z d.radical c)).trans hZcQ
  have hHX : H ≤ X d.radical a := by
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c p.start_color
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hHQ hx,
      elemPow_eq_one_of_isElementaryAbelian x ((hHU.trans (DistanceEight.U_le_Z d.radical c)) hx),hquad hx⟩
  have hTN : Q d.radical t ≤ normalizer (H : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅Z d.radical c,Q d.radical a⁆).map _ = _
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical c (hTGc hx)),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a (hTGa hx))]
  have hcore := critical_kernel_core_control s hc hb p W hWG hWN
  have hFN : W ≤ normalizer (F : Set (FreeAmalgam d.radical)) := hcore.2.2
  have hWH : W ≤ normalizer (H : Set (FreeAmalgam d.radical)) := by
    change W ≤ normalizer ((⁅Z d.radical c,Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)
    rw [hdecomp]
    exact (le_inf ((le_centralizer_iff.mp hWfix).trans (Subgroup.centralizer_le_normalizer _)) hFN).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hGH : stabilizer d.radical a ≤ normalizer (H : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    exact sup_le hTN hWH
  have hfixed := small_core_residual_fixed_knownSimple (h := h) (e := e) ha H hHQ
    ((Ltilde_le_stabilizer a).trans hGH) hcard
  exact central_false ((commutator_mono le_rfl hZwQ).trans
    ((le_inf hHX hfixed).trans (omega_fixed_central_of_small_critical s hc p hsmall a ha)))

include e hz hn in
/-- The completed order-eight selector gives either a large backward critical
image or a full critical-kernel join that the original endpoint seed does not
normalize. The latter is the precise remaining kernel-normality obstruction
in the small-image part of MS93 (5.12). -/
theorem eight_strict_backward_kernel_obstruction_knownSimple
    (hne : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g delta) (p.walk.getVert 2),
          q.walk.getVert 1 = t ∧ q.walk.getVert 2 = alpha d.radical ∧
          q.walk.getVert 3 = p.walk.getVert 1 ∧
          (4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical (act d.radical g delta)) ∨
            ¬ Z d.radical z ≤ normalizer (((Z d.radical (act d.radical g delta) ⊓
              Q d.radical (p.walk.getVert 2)) ⊔ Z d.radical (alpha d.radical) :
                Subgroup (FreeAmalgam d.radical)) : Set _)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hback := EightInitialSelection.backward_shift_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb p hsmall hdelta hstrict
  rw [show p.walk.length - 2 = 2 by omega] at hback
  obtain ⟨t,hat,g,hg,hgt,hct,hgen,hi,q,hqt,hover⟩ := hback
  have hq2 : q.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add, SimpleGraph.Walk.getVert_zero] using hover 0 (by decide)
  have hq3 : q.walk.getVert 3 = p.walk.getVert 1 := hover 1 (by decide)
  refine ⟨t,hat,g,hg,hgt,hct,hgen,hi,q,hqt,hq2,hq3,?_⟩
  by_cases hlarge : 4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex
      (Z d.radical (act d.radical g delta))
  · exact Or.inl hlarge
  refine Or.inr ?_
  intro hnorm
  have hmid : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hZzQ : Z d.radical z ≤ Q d.radical (p.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,
      SimpleGraph.dist_comm,p.dist_end,hl]
    exact hb2
  have hfix : ⁅Z d.radical (act d.radical g delta),Z d.radical (p.walk.getVert 2)⁆ ≤
      centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    (((critical_Z_commutator_le_moving (h := h) q).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)).trans
        ((commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical _ hmid)).trans (centralizer_le hZzQ))
  exact strict_small_normalized_actor_false s hc hb q (by omega) (Z d.radical z)
    (by simpa only [hqt,hq2] using hgen) (by simpa only [hq2] using hi)
    (by simpa only [hq2] using hnorm) hfix

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
