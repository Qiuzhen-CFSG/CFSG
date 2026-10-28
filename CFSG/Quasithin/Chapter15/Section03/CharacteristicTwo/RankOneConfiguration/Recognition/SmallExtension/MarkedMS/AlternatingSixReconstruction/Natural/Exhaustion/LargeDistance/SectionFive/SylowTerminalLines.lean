module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MidpointCoreLine
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardCore

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ConsecutiveSlices


public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MidpointDerivedSaturation
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalPath


/-!
# The remaining terminal line alternatives at distance six

For the literal three-shift configuration with radical image of order sixteen, the
preceding critical line cannot lie in the last backward seed. In the
nonnormalizing case this forces the restricted commutator line to be
noncentral at the endpoint and forces the full moving central attachment to
escape the last seed. Along an orbit-compatible path of length six, the
distinct-line branch is therefore impossible: the restricted commutator
coincides with the last critical line. The final theorem applies this result
to the chain generated from the actual original radical and retains its
transporter and generating-edge identity. Both covers and the original
radical maps remain literal.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.10)--(5.11), printed pp.922--923. The distance-six case is the
separate argument in (5.10); no result here identifies this graph with the
exceptional cubic graph.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


include s in
/-- A nonzero predecessor-actor commutator on the reverse critical kernel
is noncentral at the endpoint, for both moving covers. -/
theorem critical_predecessor_kernel_noncentral
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (Y : Subgroup (FreeAmalgam d.radical))
    (hYa : Y ≤ Q d.radical a)
    (hYpre : Y ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hne : ⁅Z d.radical a' ⊓ Q d.radical a,Y⁆ ≠ ⊥) :
    ¬ ⁅Z d.radical a' ⊓ Q d.radical a,Y⁆ ≤
      centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical)) := by
  intro hcentral
  have hlast := critical_last_edge_inputs (h := h) hb p
  have hYG : Y ≤ stabilizer d.radical a' :=
    (hYpre.trans hlast.2.1).trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hlast.1))
  have hAC : Z d.radical a ≤ centralizer (Y : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color)).trans (centralizer_le hYa)
  have hAF : Z d.radical a ≤ centralizer
      (U d.radical a' ⊓ Q d.radical a : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color)).trans (centralizer_le inf_le_right)
  have hdispl : ⁅U d.radical a' ⊓ Q d.radical a,Y ⊔ Z d.radical a⁆ =
      ⁅U d.radical a' ⊓ Q d.radical a,Y⁆ := by
    rw [commutator_comm,commutator_sup_fixed Y (Z d.radical a) _
      (hAC.trans (Subgroup.centralizer_le_normalizer _)) hAF,commutator_comm]
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a' p.end_color
  let A := (Z d.radical a).comap i
  let B := (Y ⊔ Z d.radical a).comap i
  have hmA : A.map i = Z d.radical a :=
    map_comap_eq_self ((Z_le_stabilizer_of_dist_le a _ p.critical.1.le).trans_eq hir.symm)
  have hmB : B.map i = Y ⊔ Z d.radical a := map_comap_eq_self
    ((sup_le hYG (Z_le_stabilizer_of_dist_le a _ p.critical.1.le)).trans_eq hir.symm)
  have hAB : A ≤ B := comap_mono le_sup_right
  have hnA : ¬ A ≤ pCore 2 d.overgroup := by
    intro hh
    have he := map_mono (f := i) hh
    rw [hmA,hiQ] at he
    exact p.critical.2 he
  have hfix : U d.radical a' ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical a' ⊓ Q d.radical a := by
    apply le_antisymm
    · intro x hx
      refine ⟨hx.1,?_⟩
      rw [←C_eq_Q s hc a p.start_color]
      exact ⟨critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
        (by rw [(replacementGeometry h d).distance_constant _ p.start_color]
            exact replacementDistance_pos h d) p.critical
          (DistanceEight.U_le_Z d.radical a' hx.1),hx.2⟩
    · exact inf_le_inf_left _ (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a p.start_color)))
  have hmF : (replacementMoved d ⊓ centralizer (A : Set d.overgroup)).map i =
      U d.radical a' ⊓ Q d.radical a := by
    rw [←map_inf_centralizer_of_injective i hi,hiU,hmA,hfix]
  have hcF : ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),B⁆ ≤ center d.overgroup := by
    intro x hx
    apply mem_center_iff.mpr
    intro m
    apply hi
    simp only [map_mul]
    apply hcentral
    · have hh := mem_map_of_mem i hx
      rw [map_commutator,hmF,hmB] at hh
      rw [hdispl] at hh
      exact commutator_mono (inf_le_inf_right _ (DistanceEight.U_le_Z d.radical a')) le_rfl hh
    · rw [←hir]
      exact ⟨m,rfl⟩
  let := finite_Z d.radical a'
  let : Finite (U d.radical a') := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a')) (inclusion_injective _)
  have hidx : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    rw [←inf_relIndex_right,inf_comm,←relIndex_map_map_of_injective _ _ hi,hmF,hiU,
      inf_relIndex_left]
    exact (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a')
      index_ne_zero_of_finite).trans_eq (small_critical_indices s hc p hsmall).2
  have hz := congrArg (Subgroup.map i) (cover_fixed_central_commutator_eq_bot s A B hAB hnA hidx hcF)
  rw [map_commutator,hmF,hmB,Subgroup.map_bot,hdispl] at hz
  have hm := (critical_kernel_predecessor_moving s hc hb p).2.2 Y hYpre
  exact hne (hm.trans hz)


include s in
/-- The preceding critical line cannot lie in the newly selected backward
seed. The generating edge would make their intersection normal and hence
force equality of the two full seeds, contrary to the shifted critical pair. -/
theorem backwardShift_critical_line_not_le_seed
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) :
    ¬ ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical q.start := by
  intro hle
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  let W := Z d.radical a ⊓ Z d.radical q.start
  have hDU : D ≤ U d.radical a :=
    (critical_Z_commutator_le_moving (h := h) p).trans inf_le_left
  have hDW : D ≤ W := le_inf (hDU.trans (DistanceEight.U_le_Z d.radical a)) hle
  have hQT : Q d.radical q.edge ≤ normalizer (W : Set (FreeAmalgam d.radical)) :=
    (le_inf
      ((show Q d.radical q.edge ≤ stabilizer d.radical a from
        fun _ hx => hx.2 _ (adjacent_symm d.radical q.adjacent_start)).trans
        (Z_normalized d.radical a))
      ((show Q d.radical q.edge ≤ stabilizer d.radical q.start from
        fun _ hx => hx.2 _ (adjacent_symm d.radical q.adjacent_shift)).trans
        (Z_normalized d.radical q.start))).trans inf_normalizer_le_normalizer_inf
  have hZW : Z d.radical a' ≤ normalizer (W : Set (FreeAmalgam d.radical)) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [commutator_comm]
    exact (commutator_mono inf_le_left le_rfl).trans hDW
  have hWN : stabilizer d.radical a ≤ normalizer (W : Set (FreeAmalgam d.radical)) := by
    rw [←q.generation]
    exact sup_le hQT hZW
  have hUW : U d.radical a ≤ W := moving_le_normal_of_noncentral s hc p.start_color
    D W hDU hDW hWN (critical_commutator_not_central s hc p)
  have hZZ : Z d.radical a ≤ Z d.radical q.start := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d p.start_color q.adjacent_start]
    exact sup_le (hUW.trans inf_le_right) (adjacent_Z_le d.radical q.path.start_color q.adjacent_shift)
  have hcard (v : Vertex d.radical) (hv : color d.radical v = false) :
      Nat.card (Z d.radical v) = Nat.card (Z d.radical (alpha d.radical)) := by
    obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical hv
    have hv' : v = act d.radical g (alpha d.radical) := by
      simpa only [alpha,act_mVertex,one_mul] using hg
    rw [hv',Z_act,card_map_of_injective (MulAut.conj _).injective]
  let := finite_Z d.radical q.start
  have heq : Z d.radical a = Z d.radical q.start := eq_of_le_of_card_ge hZZ
    (by rw [hcard a p.start_color,hcard q.start q.path.start_color])
  apply q.path.critical.2
  rw [←heq]
  apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
  rw [(replacementGeometry h d).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  change p.walk.length-2 < replacementDistance h d
  omega

include e hz hn in
/-- In the nonnormalizing terminal branch, the actual restricted-kernel
line is noncentral at the endpoint. The preceding critical line escapes the
last seed, as required in the distance-six source contradiction. -/
theorem three_shift_nonnormalized_lines_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hnorm : ¬ Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let K := Z d.radical t.start ⊓ Q d.radical v
    (¬ ⁅K,Z d.radical z ⊓ Q d.radical r.start⁆ ≤
      centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
    (¬ ⁅Z d.radical r.start,Z d.radical z⁆ ≤ Z d.radical t.start) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z d.radical t.start ⊓ Q d.radical v
  have hr := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r
  have hrs : (Q d.radical z).relIndex (Z d.radical r.start) < 4 := by rw [hr.2.1]; decide
  have hk := (SylowTerminalKernel.three_shift_kernel_control_knownSimple
    hb hcard p q r t).2.2.2.2.2 hnorm
  have hne : ⁅Z d.radical z ⊓ Q d.radical r.start,K⁆ ≠ ⊥ := by
    intro he
    rw [commutator_comm] at he
    have hh : Nat.card (⁅K,Z d.radical z ⊓ Q d.radical r.start⁆ :
        Subgroup (FreeAmalgam d.radical)) = 2 := hk.1
    rw [he,Subgroup.card_bot] at hh
    omega
  have hKQ : K ≤ Q d.radical r.start :=
    (inf_le_left.trans (neighbor_seed_le_radius t.adjacent_start t.adjacent_shift)).trans
      ((replacementGeometry h d).V_le_Q hb2 r.start r.path.start_color)
  have hn := critical_predecessor_kernel_noncentral s hc hb2 r.path hrs K hKQ inf_le_right hne
  rw [commutator_comm] at hn
  exact ⟨hn,backwardShift_critical_line_not_le_seed s hc hb2 r.path t⟩


include e hz hn in
/-- Failure of terminal normalization forces the full endpoint moving
central attachment to escape the last seed. In particular it is nontrivial;
discarding that attachment cannot prove this source branch. -/
theorem three_shift_nonnormalized_attachment_escape_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hnorm : ¬ Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    ¬ U d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) ≤
      Z d.radical t.start := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z d.radical t.start ⊓ Q d.radical v
  let F := Z d.radical z ⊓ Q d.radical r.start
  let H := ⁅K,F⁆
  let D := ⁅Z d.radical r.start,Z d.radical z⁆
  let C := Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))
  change ¬ U d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) ≤ Z d.radical t.start
  intro hattach
  have hk := (SylowTerminalKernel.three_shift_kernel_control_knownSimple
    hb hcard p q r t).2.2.2.2.2 hnorm
  have hlines := three_shift_nonnormalized_lines_knownSimple hb hcard p q r t hnorm
  have hr := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r
  have hcardD : Nat.card D = 2 := hr.2.2.2.1
  have hvz : (cosetGraph d.radical).dist v z = 2 := by
    rw [r.path.dist_end]
    have hl : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
    omega
  have hKG : K ≤ stabilizer d.radical z := inf_le_right.trans
    (Q_le_stabilizer_of_dist_two d.radical v z t.path.end_color hvz)
  have hHU : H ≤ U d.radical z := by
    dsimp only [H,F]
    rw [(critical_kernel_predecessor_moving s hc hb2 r.path).2.2 K inf_le_right
      |> fun hh => (by simpa only [commutator_comm K] using hh :
        ⁅K,Z d.radical z ⊓ Q d.radical r.start⁆ = ⁅K,U d.radical z ⊓ Q d.radical r.start⁆)]
    exact (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (hKG.trans (U_normalized z)))
  have hDU : D ≤ U d.radical z :=
    (critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right
  have hDG : D ≤ stabilizer d.radical z :=
    (hDU.trans (DistanceEight.U_le_Z d.radical z)).trans (Z_le_stabilizer d.radical z)
  have hCN : C ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    (inf_le_right.trans (centralizer_le hDG)).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨x,hx,hxc⟩ := SetLike.not_le_iff_exists.mp hlines.1
  have hxprod : x ∈ (D : Set (FreeAmalgam d.radical)) * (C : Set (FreeAmalgam d.radical)) := by
    rw [←coe_mul_of_right_le_normalizer_left D C hCN]
    exact hk.2.2 hx
  obtain ⟨a,ha,c,hcC,hac⟩ := hxprod
  have hcU : c ∈ U d.radical z := by
    have he : c = a⁻¹*x := by rw [←hac]; simp
    rw [he]
    exact (U d.radical z).mul_mem ((U d.radical z).inv_mem (hDU ha)) (hHU hx)
  have hcT : c ∈ Z d.radical t.start := by
    exact hattach ⟨hcU,hcC.2⟩
  have haT : a ∈ Z d.radical t.start := by
    have he : a = x*c⁻¹ := by rw [←hac]; simp
    rw [he]
    exact (Z d.radical t.start).mul_mem (hk.2.1 hx).1 ((Z d.radical t.start).inv_mem hcT)
  have hane : a ≠ 1 := by
    intro ha1
    apply hxc
    rw [←hac,ha1]
    simp
    exact hcC.2
  let := finite_Z d.radical z
  let : Finite D := Finite.of_injective
    (inclusion (hDU.trans (DistanceEight.U_le_Z d.radical z))) (inclusion_injective _)
  let : Finite (D ⊓ Z d.radical t.start : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hne : D ⊓ Z d.radical t.start ≠ ⊥ := by
    intro he
    have hh : a ∈ D ⊓ Z d.radical t.start := ⟨ha,haT⟩
    rw [he,mem_bot] at hh
    exact hane hh
  have hlo := (one_lt_card_iff_ne_bot (D ⊓ Z d.radical t.start)).mpr hne
  have heq : D ⊓ Z d.radical t.start = D := eq_of_le_of_card_ge inf_le_left (by omega)
  have hDle : D ≤ Z d.radical t.start := by
    rw [← heq]
    exact inf_le_right
  exact hlines.2 hDle

include e hz hn in
/-- At distance six, the distinct-line alternative is impossible on an
actual orbit-compatible shift chain. Any remaining nonnormalizing branch
has coincident restricted and last critical lines, and its full endpoint
moving central attachment escapes the last seed. -/
theorem six_nonnormalized_coincident_lines_knownSimple
    (hb : replacementDistance h d = 6)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d))
    (hnorm : ¬ Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    ⁅Z d.radical t.start ⊓ Q d.radical v,Z d.radical z ⊓ Q d.radical r.start⁆ =
      ⁅Z d.radical t.start,Z d.radical v⁆ ∧
    ¬ U d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) ≤
      Z d.radical t.start := by
  have hb4 : 4 < replacementDistance h d := by omega
  have he := three_shift_nonnormalized_attachment_escape_knownSimple hb4 hcard p q r t hnorm
  refine ⟨?_,he⟩
  rcases SylowTerminalPath.three_shift_attachment_along_path_knownSimple
    hb4 hcard p q r t hr hnorm with hh | hh
  · exact hh
  · have hl : r.path.walk.length = 6 := r.path.length_eq_b.trans hb
    have hi := hh.2 1 (by omega)
    have hc := SylowTerminalIntersection.three_shift_kernel_central_decomposition_knownSimple
      hb4 hcard p q r t
    have hend : r.path.walk.getVert (4*1+2) = q.path.walk.getVert (q.path.walk.length-2) := by
      rw [show 4*1+2 = r.path.walk.length by omega,r.path.walk.getVert_length]
    rw [hend] at hi
    exact (he (hi ▸ hc.1.trans (DistanceEight.U_le_Z d.radical t.start))).elim

include e hz hn in
/-- The distance-six terminal line alternatives applied to the shift chain
constructed from the actual original radical. The source transporter and its
generating edge remain part of the conclusion. -/
theorem original_radical_six_nonnormalized_knownSimple
    (hb : replacementDistance h d = 6)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    ∃ (q₀ : BackwardShift (h := h) p),
      act d.radical q₀.transporter (beta d.radical) = q₀.edge ∧
      T.map (MulAut.conj q₀.transporter⁻¹).toMonoidHom = Q d.radical q₀.edge ∧
      T.map (MulAut.conj q₀.transporter⁻¹).toMonoidHom ⊔ Z d.radical a' =
        stabilizer d.radical (alpha d.radical) ∧
      ∃ c c', ∃ v₀ : CriticalPath d.radical (replacementGeometry h d) c c',
      SylowTerminalPath.ShiftChain (h := h) q₀.path v₀ (replacementDistance h d) ∧
      ∃ (q : BackwardShift (h := h) v₀)
        (r : BackwardShift (h := h) q.path)
        (t : BackwardShift (h := h) r.path),
      SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d) ∧
      (¬ Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤
          normalizer
            (((Z d.radical t.start ⊓
              Q d.radical (r.path.walk.getVert (r.path.walk.length-2))) ⊔
              Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) :
                Set (FreeAmalgam d.radical)) →
        let z := q.path.walk.getVert (q.path.walk.length-2)
        let v := r.path.walk.getVert (r.path.walk.length-2)
        ⁅Z d.radical t.start ⊓ Q d.radical v,Z d.radical z ⊓ Q d.radical r.start⁆ =
          ⁅Z d.radical t.start,Z d.radical v⁆ ∧
        ¬ U d.radical z ⊓ centralizer
          (stabilizer d.radical z : Set (FreeAmalgam d.radical)) ≤ Z d.radical t.start) := by
  have hb4 : 4 < replacementDistance h d := by omega
  obtain ⟨q₀,hqact,hqmap,hqgen,c,c',v₀,hchain,q,r,t,hr,_hspan,_hdisjoint,
      _hindex,_hcentral_t,_hcentral_z,_hcentral_all, _hnon⟩ :=
    SylowTerminalPath.original_radical_terminal_path_knownSimple hb4 hcard p hfirst
  refine ⟨q₀,hqact,hqmap,hqgen,c,c',v₀,hchain,q,r,t,hr,?_⟩
  intro hnorm
  exact six_nonnormalized_coincident_lines_knownSimple hb hcard v₀ q r t hr hnorm

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
