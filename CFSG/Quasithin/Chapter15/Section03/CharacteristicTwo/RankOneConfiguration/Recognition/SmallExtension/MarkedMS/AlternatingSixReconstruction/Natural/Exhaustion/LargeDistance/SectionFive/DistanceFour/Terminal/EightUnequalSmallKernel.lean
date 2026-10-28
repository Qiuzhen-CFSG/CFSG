module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightUnequal
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelNormalization
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowUnequalResidual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSmallMovers

/-!
# The omitted-core unequal mover on a small backward critical path

Full omega central generation excludes containment of the midpoint core in
an unequal opposite mover. The same selected edge therefore generates the
midpoint residual with the original endpoint seed. The midpoint core fixes
the backward critical line; the index-two critical-line fixer then forces
the whole selected edge core to fix that line whenever the opposite mover
omits the midpoint core.

All statements retain the literal replacement graph and its full seeds.
Source: MS93 (5.5)(c) and (5.12)(1), printed pp.915,924--925.
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
  {d : Replacement L R}

include e hz hn in
/-- The omitted starting core supplies source (5.5)(c) for the actual mover
and the actual generating actor. -/
theorem eight_opposite_residual_of_core_not_le_knownSimple
    (hne₀ : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (A : Subgroup (FreeAmalgam d.radical))
    (hgen : Q d.radical t ⊔ A = stabilizer d.radical a)
    (hnot : ¬ Q d.radical a ≤ EightEdgeComparison.edgeMover (d := d) c t) :
    (EightEdgeComparison.edgeMover (d := d) c t ⊔ A).relIndex (stabilizer d.radical a) ≤ 2 ∧
      Ltilde d.radical a ≤ EightEdgeComparison.edgeMover (d := d) c t ⊔ A := by
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    cases he : color d.radical t <;> simp_all
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  obtain ⟨_,_,_,hET,_,hEi,_⟩ := EightMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hcard hb hc hct
  let := finite_stabilizer d.radical a
  exact SectionFive.index_two_opposite_generation (stabilizer d.radical a)
    (Q d.radical a) (Q d.radical t) (EightEdgeComparison.edgeMover (d := d) c t) A
    (Q_le_adjacent_h d.radical ht hat)
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat)) hET (Q_normalized d.radical a)
    hEi hnot hgen

include e hz hn in
/-- Global central generation discharges the omitted-core premise of the
same-mover residual theorem on the selected unequal edge. -/
theorem eight_unequal_residual_of_central_generation_knownSimple
    (hne₀ : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : EightEdgeComparison.edgeMover (d := d) c t ≠ EightEdgeComparison.edgeMover (d := d) a t)
    (A : Subgroup (FreeAmalgam d.radical))
    (hgen : Q d.radical t ⊔ A = stabilizer d.radical a)
    (hsplit : X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))) :
    (¬ Q d.radical a ≤ EightEdgeComparison.edgeMover (d := d) c t) ∧
      Ltilde d.radical a ≤ EightEdgeComparison.edgeMover (d := d) c t ⊔ A := by
  have hnot : ¬ Q d.radical a ≤ EightEdgeComparison.edgeMover (d := d) c t := fun hcore =>
    EightUnequal.unequal_containing_core_not_centrally_generated_knownSimple
      hne₀ hcard hb ha hat hct hne hcore hsplit
  exact ⟨hnot,(eight_opposite_residual_of_core_not_le_knownSimple
    hne₀ hcard (by omega) ha hat hct A hgen hnot).2⟩

include e hz hn in
/-- The small-mover maximum fixes the critical line and normalizes the full
critical kernel. When the line moves, it is exactly the relative kernel normalizer. -/
private theorem eight_small_critical_kernel_small_movers_knownSimple
    (hne₀ : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a
    let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
    J.relIndex T = 2 ∧
      J ≤ centralizer ((⁅Z d.radical a,Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      J ≤ normalizer ((Z d.radical a ⊓ Q d.radical a' : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ((¬ T ≤ centralizer ((⁅Z d.radical a,Z d.radical a'⁆ :
          Subgroup (FreeAmalgam d.radical)) : Set _)) →
        T ⊓ normalizer ((Z d.radical a ⊓ Q d.radical a' :
          Subgroup (FreeAmalgam d.radical)) : Set _) = J) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let t := p.walk.getVert 1
  let T := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
  let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨J₀,_,hJ₀,_,hJT,_,hJi,_,hact⟩ := Nonelementary.edge_normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hb p.start_color hat
  change J = J₀ at hJ₀
  rw [←hJ₀] at hJT hJi hact
  have hAt : Z d.radical a' ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [(replacementGeometry h d).distance_constant a' p.end_color,SimpleGraph.dist_comm,p.dist_end]
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-1 < replacementDistance h d
    omega
  have hidx : (centralizer (Z d.radical a' : Set _)).relIndex (U d.radical a) ≤ 2 := by
    let := finite_Z d.radical a
    let : Finite (U d.radical a) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
    have hC := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color))
    exact ((relIndex_le_of_le_left hC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a) index_ne_zero_of_finite)).trans_eq
      (small_critical_indices s hc p hsmall).1
  have hcomm : ⁅J,Z d.radical a'⁆ ≤ centralizer (Z d.radical a : Set _) :=
    (hact _ hAt hidx).2.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color)))
  have hAG := critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
    (by rw [(replacementGeometry h d).distance_constant a p.start_color]
        exact replacementDistance_pos h d) p.critical
  have hJn : J ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
    dsimp only [D]
    rw [commutator_comm (Z d.radical a)]
    exact SylowNormalizer.fixed_mod_central_normalizes (Z d.radical a') (Z d.radical a) J
      (hAG.trans (Z_normalized d.radical a))
      ((hJT.trans inf_le_right).trans (Z_normalized d.radical a)) hcomm
  have hJc : J ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
    hJn.trans (normalizer_le_centralizer_of_card_two _
      (small_critical_commutator_card s hc p hsmall))
  have hJk : J ≤ normalizer
      ((Z d.radical a ⊓ Q d.radical a' : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    have hh := le_inf (hJT.trans inf_le_right) hJc
    rw [←small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall] at hh
    exact hh.trans inf_le_right
  refine ⟨hJi,hJc,hJk,?_⟩
  intro hmove
  let H := T ⊓ normalizer
    ((Z d.radical a ⊓ Q d.radical a' : Subgroup (FreeAmalgam d.radical)) : Set _)
  have hJH : J ≤ H := le_inf hJT hJk
  have hHG : H ≤ stabilizer d.radical a := inf_le_left.trans inf_le_right
  have hHC : H ≤ centralizer (D : Set (FreeAmalgam d.radical)) := by
    have hh := le_inf hHG (show H ≤ normalizer
      ((Z d.radical a ⊓ Q d.radical a' : Subgroup (FreeAmalgam d.radical)) : Set _) from inf_le_right)
    rw [small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall] at hh
    exact hh.trans inf_le_right
  let := finite_stabilizer d.radical a
  let : Finite T := Finite.of_injective (inclusion (show T ≤ stabilizer d.radical a from inf_le_right))
    (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion (show H ≤ T from inf_le_left)) (inclusion_injective _)
  have hpos : 0 < H.relIndex T := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hne : H.relIndex T ≠ 1 := fun he => hmove ((relIndex_eq_one.mp he).trans hHC)
  have hjpos : 0 < J.relIndex H := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have htwo : 2 ≤ H.relIndex T := by omega
  have hi := relIndex_mul_relIndex J H T hJH inf_le_left
  rw [hJi] at hi
  have he : J.relIndex H = 1 := by nlinarith
  exact le_antisymm (relIndex_eq_one.mp he) hJH


include e hz hn in
/-- Restriction of the relative-normalizer calculation to the literal
image-eight edge core, at distance four as well as above four. -/
theorem eight_small_critical_edge_mover_control_knownSimple
    (hne₀ : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4) :
    let T := Q d.radical (p.walk.getVert 1)
    let J := EightEdgeComparison.edgeMover (d := d) a (p.walk.getVert 1)
    J ≤ centralizer ((⁅Z d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      J ≤ normalizer ((Z d.radical a ⊓ Q d.radical z : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ((¬ T ≤ centralizer ((⁅Z d.radical a,Z d.radical z⁆ :
          Subgroup (FreeAmalgam d.radical)) : Set _)) →
        T ⊓ centralizer ((⁅Z d.radical a,Z d.radical z⁆ :
          Subgroup (FreeAmalgam d.radical)) : Set _) = J) := by
  let T := Q d.radical (p.walk.getVert 1)
  let J := EightEdgeComparison.edgeMover (d := d) a (p.walk.getVert 1)
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨hJ,_,_,hJT,_,_,_⟩ := EightMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hcard hb p.start_color hat
  have hk := eight_small_critical_kernel_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hb p hsmall
  have hJC : J ≤ centralizer ((⁅Z d.radical a,Z d.radical z⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _) := hJ.le.trans (inf_le_right.trans hk.2.1)
  have hJN := hJ.le.trans (inf_le_right.trans hk.2.2.1)
  refine ⟨hJC,hJN,?_⟩
  intro hmove
  have hmoveN : ¬ (normalizer (T : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a) ≤
      centralizer ((⁅Z d.radical a,Z d.radical z⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hh
    exact hmove ((le_inf T.le_normalizer (fun _ hx => hx.2 a (adjacent_symm d.radical hat))).trans hh)
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have he : T ⊓ normalizer ((Z d.radical a ⊓ Q d.radical z :
      Subgroup (FreeAmalgam d.radical)) : Set _) = J := by
    rw [show J = _ from hJ,←hk.2.2.2 hmoveN,←inf_assoc,
      inf_eq_left.mpr (le_inf T.le_normalizer (fun _ hx => hx.2 a (adjacent_symm d.radical hat)))]
  change T ⊓ centralizer ((⁅Z d.radical a,Z d.radical z⁆ :
    Subgroup (FreeAmalgam d.radical)) : Set _) = J
  rw [←he]
  have hTG : T ≤ stabilizer d.radical a := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hh := congrArg (fun A : Subgroup (FreeAmalgam d.radical) => T ⊓ A)
    (small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall)
  simpa only [←inf_assoc,inf_eq_left.mpr hTG] using hh.symm

include e hz hn in
/-- In the omitted-core branch the edge core fixes the backward critical
line. Otherwise its index-two line fixer would contain the whole midpoint core. -/
theorem eight_omitted_midpoint_core_fixes_critical_line_knownSimple
    (hne₀ : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {c z : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical c) < 4)
    (hnot : ¬ Q d.radical (q.walk.getVert 2) ≤
      EightEdgeComparison.edgeMover (d := d) c (q.walk.getVert 1)) :
    Q d.radical (q.walk.getVert 1) ≤
      centralizer ((⁅Z d.radical c,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  by_contra hmove
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let a := q.walk.getVert 2
  let t := q.walk.getVert 1
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb
  have ha : color d.radical a = false := (q.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical a t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hVc : Z d.radical c ≤ V d.radical a :=
    le_iSup_of_le c (le_iSup_of_le (by rw [q.dist_start (by omega)]) le_rfl)
  have hVz : Z d.radical z ≤ V d.radical a :=
    le_iSup_of_le z (le_iSup_of_le (by rw [SimpleGraph.dist_comm,q.dist_end,hl]) le_rfl)
  have hDX : ⁅Z d.radical c,Z d.radical z⁆ ≤ X d.radical a :=
    (commutator_mono hVc hVz).trans (radius_bounds_general s hc hb2 ha c z).2.1
  have hfix : Q d.radical a ≤ centralizer ((⁅Z d.radical c,Z d.radical z⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _) :=
    le_centralizer_iff.mp (hDX.trans (fun _ hx => (mem_omegaCenter_iff.mp hx).2.2))
  apply hnot
  rw [←(eight_small_critical_edge_mover_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hcard hb2 q hsmall).2.2 hmove]
  exact le_inf (Q_le_adjacent_h d.radical ht hat) hfix

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
