module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenUnequalSmallFixed
public import Theory.GroupTheory.PerfectHalfOrderImage
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenUnequal

/-!
# The actual unequal failure line fixes the full derived stabilizer

The source generation argument constructs a subgroup of index at most two,
consisting of the opposite small mover and the critical endpoint seed. Both
actors centralize the full backward-kernel failure line. Retaining the index
bound therefore makes the entire derived starting stabilizer fix that line.
This strengthens the residual-only output without requiring extra fixation,
omega-center placement, or an abelian residual quotient.

Source: MS93 (5.5)(c), (5.12)(1), printed pp.915,924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
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

private theorem derived_le_of_relIndex_le_two {F : Type*} [Group F]
    (P Y : Subgroup F) [Finite P] (hi : Y.relIndex P ≤ 2) : ⁅P,P⁆ ≤ Y := by
  have hh := map_mono (f := P.subtype)
    (PerfectHalfOrderImage.commutator_le_of_index_le_two (Y.subgroupOf P) hi)
  rw [map_subtype_commutator] at hh
  exact hh.trans (map_comap_le P.subtype Y)

include e hz hn in
/-- The actual opposite mover and endpoint seed fix the entire failure line
under the derived subgroup of the starting stabilizer. The index-two bound
is retained from the source generation proof, beyond residual fixation. -/
theorem unequal_failure_line_derived_fixed_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hne : SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical (q.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (q.walk.getVert 1)) 4)
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z = stabilizer d.radical a)
    (hbad : ¬ Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ⁅Z d.radical c ⊓ Q d.radical (p.walk.getVert 2),Z d.radical z ⊓ Q d.radical a⁆ ≤
      centralizer ((⁅stabilizer d.radical a,stabilizer d.radical a⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  let t := q.walk.getVert 1
  let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
  let H := ⁅Z d.radical c ⊓ Q d.radical (p.walk.getVert 2),Z d.radical z ⊓ Q d.radical a⁆
  have hca : (cosetGraph d.radical).dist c a ≤ 2 := by
    rw [←hq2,q.dist_start (by omega)]
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a t := by
    rw [←hq2]
    exact adjacent_symm d.radical
      ((cosetGraph_adj d.radical _ _).mp (q.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨hXall,_,hHseeds⟩ := small_backward_kernel_nonnormal_three_seed_line
    s hc hb p hsmall q.start_color hca hbad
  have hnot : ¬ Q d.radical a ≤ E := fun hcore =>
    SixteenUnequal.sixteen_unequal_containing_core_not_centrally_generated_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 hcard p.start_color hat hct hne hcore
        (hXall a p.start_color)
  have hindex : (E ⊔ Z d.radical z).relIndex (stabilizer d.radical a) ≤ 2 :=
    (SixteenUnequal.sixteen_opposite_residual_of_core_not_le_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 hcard p.start_color hat hct
        (Z d.radical z) hgen hnot).1
  have hHE : H ≤ centralizer (E : Set (FreeAmalgam d.radical)) := by
    have hh := SixteenSmall.nonelementary_backward_kernel_mover_fixed_knownSimple
      (e := e) (hz := hz) (hn := hn) (SixteenUnequal.sixteen_nonelementary hcard) hb p q hq2
    rw [SylowLarge.sixteen_edge_relative_normalizer_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 hcard q.start_color hct] at hh
    exact hh
  have hHZ : H ≤ Z d.radical z := hHseeds.trans inf_le_right
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) z p.end_color
  have hHcentral : H ≤ centralizer ((E ⊔ Z d.radical z : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hHE) (le_centralizer_iff.mp
      (hHZ.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)))
  let := finite_stabilizer d.radical a
  exact hHcentral.trans (centralizer_le (derived_le_of_relIndex_le_two _ _ hindex))

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
