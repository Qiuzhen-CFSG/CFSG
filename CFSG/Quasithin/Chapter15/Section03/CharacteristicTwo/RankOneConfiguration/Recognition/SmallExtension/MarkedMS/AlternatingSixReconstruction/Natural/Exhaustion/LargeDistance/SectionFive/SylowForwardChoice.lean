module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowForwardKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSixteenEscape
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSpanCollapse
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSpanSelection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion

/-!
# Independence of the forward seed-kernel line

Two aligned nonzero kernel commutators from the starting radius coincide.
Join both actors to the starting seed: above distance four this is an actual
elementary subgroup. Both actors lie in the same endpoint edge radical.
The aligned target centralizes their join because their starting radius lies
in the starting core; no edge-wide centrality of the critical line is used.
If full displacement were controlled, aligned-actor rigidity would annihilate
the nonzero kernel commutator. Elementary-actor control therefore bounds the
combined kernel commutator by two and identifies both nonzero subgroups.

The literal source (5.9) application compares every two admissible component
choices on the same forward critical path, using the already constructed
seed orbits and their actual predecessor-core containment. Neither the
radical image nor the whole edge core is assumed elementary. Both natural
covers and the full fixed attachment remain in the alignment target.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3) and (5.9), printed pp.866--867 and 921. Centrality of the line
under the whole starting stabilizer and control of the larger span remain
source obligations; choice independence alone does not assert them.
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

/-- Aligned nonzero kernel commutators of two subactors of the actual radius
are the same line. The combined elementary actor supplies the bound. -/
theorem aligned_radius_kernel_line_unique
    (hc : DistanceTwo.CentralLayer d) (hb : 4 < replacementDistance h d)
    {c z t : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical c) < 4)
    (hzt : Adjacent d.radical z t) (hct : Z d.radical c ≤ Q d.radical t)
    (P₁ P₂ : Subgroup (FreeAmalgam d.radical))
    (hPV₁ : P₁ ≤ V d.radical c) (hPV₂ : P₂ ≤ V d.radical c)
    (hPt₁ : P₁ ≤ Q d.radical t) (hPt₂ : P₂ ≤ Q d.radical t)
    (hne₁ : ⁅Z d.radical z ⊓ Q d.radical c,P₁⁆ ≠ ⊥)
    (hne₂ : ⁅Z d.radical z ⊓ Q d.radical c,P₂⁆ ≠ ⊥)
    (halign₁ : ⁅Z d.radical z ⊓ Q d.radical c,P₁⁆ ≤
      ⁅Z d.radical c,Z d.radical z⁆ ⊔
        (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))))
    (halign₂ : ⁅Z d.radical z ⊓ Q d.radical c,P₂⁆ ≤
      ⁅Z d.radical c,Z d.radical z⁆ ⊔
        (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)))) :
    ⁅Z d.radical z ⊓ Q d.radical c,P₁⁆ = ⁅Z d.radical z ⊓ Q d.radical c,P₂⁆ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let K := Z d.radical z ⊓ Q d.radical c
  let P := (P₁ ⊔ P₂) ⊔ Z d.radical c
  let J := ⁅K,P⁆
  let T := ⁅Z d.radical c,Z d.radical z⁆ ⊔
    (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)))
  have hPV : P ≤ V d.radical c := sup_le (sup_le hPV₁ hPV₂) (Z_le_VBall d.radical c 2)
  have hPQ : P ≤ Q d.radical c := hPV.trans
    ((replacementGeometry h d).V_le_Q hb2 c q.start_color)
  have hPt : P ≤ Q d.radical t := sup_le (sup_le hPt₁ hPt₂) hct
  have hPG : P ≤ stabilizer d.radical z :=
    hPt.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hzt))
  have hcrit : ⁅Z d.radical c,Z d.radical z⁆ ≤ Z d.radical c :=
    ((critical_Z_commutator_le_moving (h := h) q).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical c)
  have hZQ := commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c q.start_color)
  have hTC : T ≤ centralizer (P : Set (FreeAmalgam d.radical)) :=
    sup_le (hcrit.trans (hZQ.trans (centralizer_le hPQ)))
      (inf_le_right.trans (centralizer_le hPG))
  have hPN : P ≤ normalizer (T : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp hTC).trans (Subgroup.centralizer_le_normalizer _)
  have h₁ : P₁ ≤ P := le_sup_left.trans le_sup_left
  have h₂ : P₂ ≤ P := le_sup_right.trans le_sup_left
  have hJT : J ≤ T := by
    rw [show J = ⁅K,(P₁ ⊔ P₂) ⊔ Z d.radical c⁆ from rfl,commutator_comm]
    apply commutator_sup_le_of_relative_normal P (P₁ ⊔ P₂) (Z d.radical c)
      K T hPN le_sup_left le_sup_right
    · exact commutator_sup_le_of_relative_normal P P₁ P₂ K T hPN h₁ h₂
        (by rwa [commutator_comm]) (by rwa [commutator_comm])
    · exact (commutator_mono le_rfl inf_le_right).trans
        ((Z_centralizes_Q d.radical c q.start_color).le.trans bot_le)
  have hfixed := critical_full_kernel_eq s hc q
  have hfail : ¬ ⁅Z d.radical z,P⁆ ≤
      ⁅Z d.radical z ⊓ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)),P⁆ ⊔
        ⁅Z d.radical z,Z d.radical c⁆ := by
    intro hh
    rw [←hfixed,commutator_comm (Z d.radical z) (Z d.radical c)] at hh
    have hwhole : ⁅U d.radical z,P⁆ ≤ T :=
      (commutator_mono (DistanceEight.U_le_Z d.radical z) le_rfl).trans
        (hh.trans (sup_le hJT le_sup_left))
    have hz := small_critical_aligned_kernel_commutator_eq_bot s hc q hsmall P hPG hwhole
    exact hne₁ (le_bot_iff.mp ((commutator_mono le_rfl h₁).trans_eq hz))
  have hindex : (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ 2 := by
    let := finite_Z d.radical z
    let : Finite (U d.radical z) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
    have hQC : Q d.radical c ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp hZQ
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc q hsmall).2
  let := V_elementary_of_four_lt d.radical q.start_color hb
  have he : IsElementaryAbelian 2 P := IsElementaryAbelian.of_le hPV
  have hbound := (elementary_edge_kernel_small_aligned s hc q.end_color hzt
    (Z d.radical c) P hct hPt le_sup_right he q.critical.2 hindex hfail).1
  rw [←hfixed] at hbound
  have hJZ : J ≤ Z d.radical z :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hPG.trans (Z_normalized d.radical z)))
  let := finite_Z d.radical z
  let : Finite J := Finite.of_injective (inclusion hJZ) (inclusion_injective _)
  have hJ₁ : ⁅K,P₁⁆ ≤ J := commutator_mono le_rfl h₁
  have hJ₂ : ⁅K,P₂⁆ ≤ J := commutator_mono le_rfl h₂
  let : Finite (⁅K,P₁⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hJ₁) (inclusion_injective _)
  let : Finite (⁅K,P₂⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hJ₂) (inclusion_injective _)
  have hi₁ := (one_lt_card_iff_ne_bot ⁅K,P₁⁆).mpr hne₁
  have hi₂ := (one_lt_card_iff_ne_bot ⁅K,P₂⁆).mpr hne₂
  have hcard : Nat.card J ≤ 2 := hbound
  exact (eq_of_le_of_card_ge hJ₁ (by omega)).trans (eq_of_le_of_card_ge hJ₂ (by omega)).symm

private theorem shifted_seed_orbit_kernel_data
    (hc : DistanceTwo.CentralLayer d) (hb : 4 < replacementDistance h d)
    {a' z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hindex : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) = 2)
    (q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) z)
    (hdist : (cosetGraph d.radical).dist a' z = 2)
    (hpre : q.walk.getVert (q.walk.length-2) = a')
    (hqsmall : (Q d.radical z).relIndex (Z d.radical (p.walk.getVert 2)) < 4)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical (p.walk.getVert 2)) :
    let c := p.walk.getVert 2
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical c,T⁆
    let P := stabilizer d.radical c ⊓ centralizer
      (H.map (MulAut.conj y).toMonoidHom : Set (FreeAmalgam d.radical))
    let D := conjugateSpanBy (Z d.radical (act d.radical y⁻¹ (alpha d.radical))) P
    P ⊔ Z d.radical z = stabilizer d.radical c →
    (¬ H.map (MulAut.conj y).toMonoidHom ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical))) →
    D ≤ V d.radical c ∧ D ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) ∧
      Nat.card (⁅D,Z d.radical z ⊓ Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅D,Z d.radical z ⊓ Q d.radical c⁆ ≤ ⁅Z d.radical c,Z d.radical z⁆ ⊔
        (Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
      X d.radical z = U d.radical z ⊔
        (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
  dsimp only
  intro hgen hmove
  let c := p.walk.getVert 2
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T⁆
  let P (y : FreeAmalgam d.radical) := stabilizer d.radical c ⊓
    centralizer (H.map (MulAut.conj y).toMonoidHom : Set (FreeAmalgam d.radical))
  let D (y : FreeAmalgam d.radical) :=
    conjugateSpanBy (Z d.radical (act d.radical y⁻¹ (alpha d.radical))) (P y)
  have hseed (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical c) :
      Z d.radical (act d.radical y⁻¹ (alpha d.radical)) ≤ V d.radical c ∧
      ¬ Z d.radical (act d.radical y⁻¹ (alpha d.radical)) ≤
        B d.radical c ((replacementGeometry h d).Z_normal _) := by
    constructor
    · have hl : p.walk.length = replacementDistance h d := p.length_eq_b
      have hZV : Z d.radical (alpha d.radical) ≤ V d.radical c :=
        le_iSup_of_le (alpha d.radical) (le_iSup_of_le
          (show (cosetGraph d.radical).dist (alpha d.radical) c ≤ 2 from
            (p.dist_start (by omega)).le) le_rfl)
      rw [Z_act,inv_inv]
      exact (map_mono hZV).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized d.radical c hy))
    · have hBm := mem_normalizer_iff_map_conj_eq.mp
        (Escape.Propagation.Rigidity.B_normalized (show 2 < replacementDistance h d by omega)
          _ q.start_color hy)
      intro hbad
      rw [Z_act,inv_inv,←hBm] at hbad
      have hstart := (map_le_map_iff_of_injective (MulAut.conj y).injective).mp hbad
      exact critical_start_not_le_second_slice s hc (by omega) p
        ((DistanceEight.U_le_Z d.radical _).trans hstart)
  have hDpre (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical c)
      (hgen : P y ⊔ Z d.radical z = stabilizer d.radical c)
      (hmove : ¬ H.map (MulAut.conj y).toMonoidHom ≤
        centralizer (Z d.radical z : Set (FreeAmalgam d.radical))) :
      D y ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hD,_⟩ :=
      cover_small_shifted_forward_configuration_of_choice s hc hb p hsmall hindex
        z q.end_color hdist y hy hgen hmove
    rw [hpre]
    exact hD
  let t := p.walk.getVert 1
  have hl : 2 < p.walk.length := p.length_eq_b ▸ (show 2 < replacementDistance h d by omega)
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hline (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical c)
      (hgen : P y ⊔ Z d.radical z = stabilizer d.radical c)
      (hmove : ¬ H.map (MulAut.conj y).toMonoidHom ≤
        centralizer (Z d.radical z : Set (FreeAmalgam d.radical))) :
      Nat.card (⁅D y,Z d.radical z ⊓ Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅D y,Z d.radical z ⊓ Q d.radical c⁆ ≤ ⁅Z d.radical c,Z d.radical z⁆ ⊔
        (Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
      X d.radical z = U d.radical z ⊔
        (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
    have hctx : Adjacent d.radical c (act d.radical y⁻¹ t) := by
      have hh := (adjacent_act_iff d.radical y⁻¹ c t).mpr hct
      rwa [show act d.radical y⁻¹ c = c from (stabilizer d.radical c).inv_mem hy] at hh
    have hcol : color d.radical (act d.radical y⁻¹ (alpha d.radical)) = false := by
      rw [action_preserves_color]
      rfl
    have hh := generated_seed_orbit_kernel_line s hc hb q hqsmall hcol hctx
      ((adjacent_act_iff d.radical y⁻¹ _ _).mpr hat) (P y) inf_le_left hgen
      (hseed y hy).2 (hDpre y hy hgen hmove)
    have hfull := generated_seed_orbit_full_kernel s hc hb q hqsmall hcol hctx
      ((adjacent_act_iff d.radical y⁻¹ _ _).mpr hat) (P y) inf_le_left hgen
      (hseed y hy).2 (hDpre y hy hgen hmove)
    exact ⟨hh.1,hh.2.1,hfull.1⟩
  exact ⟨conjugateSpanBy_le (hseed y hy).1
    (inf_le_left.trans (DistanceEight.V_normalized d.radical c)),
    hDpre y hy hgen hmove,hline y hy hgen hmove⟩

/-- The shifted seed-orbit line is independent of the admissible component
choice on the same literal forward critical path. -/
theorem shifted_kernel_choice_independent
    (hc : DistanceTwo.CentralLayer d) (hb : 4 < replacementDistance h d)
    {a' z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hindex : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) = 2)
    (q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) z)
    (hdist : (cosetGraph d.radical).dist a' z = 2)
    (hpre : q.walk.getVert (q.walk.length-2) = a')
    (hqsmall : (Q d.radical z).relIndex (Z d.radical (p.walk.getVert 2)) < 4)
    (y₁ y₂ : FreeAmalgam d.radical)
    (hy₁ : y₁ ∈ stabilizer d.radical (p.walk.getVert 2))
    (hy₂ : y₂ ∈ stabilizer d.radical (p.walk.getVert 2)) :
    let c := p.walk.getVert 2
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical c,T⁆
    let H₁ := H.map (MulAut.conj y₁).toMonoidHom
    let H₂ := H.map (MulAut.conj y₂).toMonoidHom
    let P₁ := stabilizer d.radical c ⊓ centralizer (H₁ : Set (FreeAmalgam d.radical))
    let P₂ := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
    let D₁ := conjugateSpanBy (Z d.radical (act d.radical y₁⁻¹ (alpha d.radical))) P₁
    let D₂ := conjugateSpanBy (Z d.radical (act d.radical y₂⁻¹ (alpha d.radical))) P₂
    P₁ ⊔ Z d.radical z = stabilizer d.radical c →
    P₂ ⊔ Z d.radical z = stabilizer d.radical c →
    (¬ H₁ ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical))) →
    (¬ H₂ ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical))) →
    ⁅D₁,Z d.radical z ⊓ Q d.radical c⁆ = ⁅D₂,Z d.radical z ⊓ Q d.radical c⁆ ∧
      ⁅D₁,X d.radical z ⊓ Q d.radical c⁆ = ⁅D₂,X d.radical z ⊓ Q d.radical c⁆ := by
  dsimp only
  intro hgen₁ hgen₂ hmove₁ hmove₂
  let c := p.walk.getVert 2
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T⁆
  let P (y : FreeAmalgam d.radical) := stabilizer d.radical c ⊓
    centralizer (H.map (MulAut.conj y).toMonoidHom : Set (FreeAmalgam d.radical))
  let D (y : FreeAmalgam d.radical) :=
    conjugateSpanBy (Z d.radical (act d.radical y⁻¹ (alpha d.radical))) (P y)
  have h₁ := shifted_seed_orbit_kernel_data s hc hb p hsmall hindex q hdist hpre hqsmall
    y₁ hy₁ hgen₁ hmove₁
  have h₂ := shifted_seed_orbit_kernel_data s hc hb p hsmall hindex q hdist hpre hqsmall
    y₂ hy₂ hgen₂ hmove₂
  have hne (y : FreeAmalgam d.radical)
      (hh : Nat.card (⁅D y,Z d.radical z ⊓ Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) = 2) :
      ⁅Z d.radical z ⊓ Q d.radical c,D y⁆ ≠ ⊥ := by
    intro he
    rw [commutator_comm,he,card_bot] at hh
    omega
  have hedge := critical_last_edge_inputs (h := h) (by omega : 2 < replacementDistance h d) q
  have hfixed : Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) ≤
      stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) :=
    inf_le_inf_right _ (Z_le_stabilizer d.radical z)
  have hh := aligned_radius_kernel_line_unique s hc hb q hqsmall hedge.1 hedge.2.2
    (D y₁) (D y₂) h₁.1 h₂.1 (h₁.2.1.trans hedge.2.1) (h₂.2.1.trans hedge.2.1)
    (hne y₁ h₁.2.2.1) (hne y₂ h₂.2.2.1)
    (by rw [commutator_comm]; exact h₁.2.2.2.1.trans (sup_le_sup_left hfixed _))
    (by rw [commutator_comm]; exact h₂.2.2.2.1.trans (sup_le_sup_left hfixed _))
  have hseedEq : ⁅D y₁,Z d.radical z ⊓ Q d.radical c⁆ =
      ⁅D y₂,Z d.radical z ⊓ Q d.radical c⁆ := by
    rw [commutator_comm (D y₁),commutator_comm (D y₂)]
    exact hh
  have hDz (y : FreeAmalgam d.radical)
      (hpreD : D y ≤ Q d.radical (q.walk.getVert (q.walk.length-2))) :
      D y ≤ stabilizer d.radical z :=
    (hpreD.trans hedge.2.1).trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hedge.1))
  have hfull₁ := (critical_X_displacements_of_central_generation s hc q h₁.2.2.2.2
    (D y₁) (hDz y₁ h₁.2.1)).2
  have hfull₂ := (critical_X_displacements_of_central_generation s hc q h₁.2.2.2.2
    (D y₂) (hDz y₂ h₂.2.1)).2
  exact ⟨hseedEq,hfull₁.trans (hseedEq.trans hfull₂.symm)⟩

end SylowForwardKernel
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
