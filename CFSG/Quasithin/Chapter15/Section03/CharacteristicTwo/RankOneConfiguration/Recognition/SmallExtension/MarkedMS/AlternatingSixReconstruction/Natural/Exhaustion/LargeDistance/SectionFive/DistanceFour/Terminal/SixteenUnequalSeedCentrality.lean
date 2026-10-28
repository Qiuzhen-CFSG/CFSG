module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenEqualSecondBackward
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenReverseStrict
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenUnequal
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowPairedFixer

/-!
# Unequal backward seeds in the order-sixteen case

A strict forward Baumann slice makes the common seed fixed by both endpoint
movers. Distinct movers have index two in the edge core, so they generate it.
The common seed is therefore the edge omega center. Applied to the actual
backward critical commutator, this supplies the centrality at the original
starting vertex used in MS93 (5.12)(1), printed p.925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "edgeMover" => fun a t : Vertex d.radical =>
  SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4

private theorem unequal_index_two_sup {F : Type*} [Group F]
    (J E T : Subgroup F) (hJT : J ≤ T) (hET : E ≤ T)
    (hJi : J.relIndex T = 2) (hEi : E.relIndex T = 2) (hne : E ≠ J) :
    J ⊔ E = T := by
  have hST : J ⊔ E ≤ T := sup_le hJT hET
  have hm := relIndex_mul_relIndex J (J ⊔ E) T le_sup_left hST
  rw [hJi] at hm
  have hd : J.relIndex (J ⊔ E) ∣ 2 := ⟨(J ⊔ E).relIndex T, by omega⟩
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with he | he
  · have hEJ : E ≤ J := le_sup_right.trans (relIndex_eq_one.mp he)
    have hm' := relIndex_mul_relIndex E J T hEJ hJT
    rw [hEi,hJi] at hm'
    have hone : E.relIndex J = 1 := by omega
    exact (hne (le_antisymm hEJ (relIndex_eq_one.mp hone))).elim
  · rw [he] at hm
    have hone : (J ⊔ E).relIndex T = 1 := by omega
    exact le_antisymm hST (relIndex_eq_one.mp hone)

include e hz hn in
/-- Unequal movers and the original forward strict slice identify the whole
neighboring seed intersection with the edge omega center. -/
theorem sixteen_unequal_strict_seed_intersection_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : edgeMover c t ≠ edgeMover a t)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    Z d.radical a ⊓ Z d.radical c = Z d.radical t := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hXall := sixteen_small_omega_centrally_generated_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard hb
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases hh' : color d.radical c <;> simp_all
  have hfixA := SixteenSmall.sixteen_forward_strict_seed_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard hb2 ha hat hct (hXall a ha) hstrict
  have hfixC := SixteenSmall.sixteen_reverse_strict_seed_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard hb2 hc hct hat (hXall c hc) hstrict
  rw [inf_comm (Z d.radical c) (Z d.radical a)] at hfixC
  obtain ⟨_,hJT,_,hJi,_⟩ := SixteenUnequal.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 hcard ha hat
  obtain ⟨_,hET,_,hEi,_⟩ := SixteenUnequal.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 hcard hc hct
  have hsup := unequal_index_two_sup _ _ _ hJT hET hJi hEi hne
  have hfix : Z d.radical a ⊓ Z d.radical c ≤
      centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    rw [←hsup]
    exact sup_le (le_centralizer_iff.mp hfixA)
      (le_centralizer_iff.mp hfixC)
  apply le_antisymm
  · intro x hx
    have hXa : Z d.radical a ≤ X d.radical a := by
      apply (replacementGeometry h d).omega_bound a ha
      rw [(replacementGeometry h d).distance_constant a ha]
      exact replacementDistance_pos h d
    obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp (hXa hx.1)
    rw [Z,if_neg (by simp [ht])]
    exact mem_omegaCenter_iff.mpr ⟨Q_le_adjacent_h d.radical ht hat hxQ,hx2,hfix hx⟩
  · exact le_inf (adjacent_Z_le d.radical ha hat) (adjacent_Z_le d.radical hc hct)

include e hz hn in
/-- The unequal first backward critical commutator is central at the original
starting vertex, using its literal edge/endpoint generation identity. -/
theorem sixteen_unequal_backward_commutator_central_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hne : edgeMover c (q.walk.getVert 1) ≠ edgeMover a (q.walk.getVert 1))
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z = stabilizer d.radical a)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hpl : p.walk.length = 4 := p.length_eq_b.trans hb
  let t := q.walk.getVert 1
  let v := p.walk.getVert 2
  let H := ⁅Z d.radical c,Z d.radical v⁆
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a t := by
    rw [←hq2]
    exact adjacent_symm d.radical
      ((cosetGraph_adj d.radical _ _).mp (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have hXall := sixteen_small_omega_centrally_generated_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard hb
  have hXZ := SylowPairedFixer.central_generation_eq_seed
    (h := h) p.start_color hat (hXall a p.start_color)
  have hHZ : H ≤ Z d.radical a := by
    rw [←hXZ]
    have hcV : Z d.radical c ≤ V d.radical a :=
      le_iSup_of_le c (le_iSup_of_le (by rw [←hq2,q.dist_start (by omega)]) le_rfl)
    have hvV : Z d.radical v ≤ V d.radical a :=
      le_iSup_of_le v (le_iSup_of_le (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)]) le_rfl)
    exact (commutator_mono hcV hvV).trans
      (radius_bounds_general s hc hb2 p.start_color c v).2.1
  have hHc : H ≤ Z d.radical c :=
    ((critical_Z_commutator_le_moving (h := h) q).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical c)
  have hinter := sixteen_unequal_strict_seed_intersection_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard hb p.start_color hat hct hne hstrict
  have hHt : H ≤ Z d.radical t := (le_inf hHZ hHc).trans hinter.le
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hHT : H ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro x hx
    have hh := hHt hx
    rw [Z,if_neg (by simp [ht])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  have hv : color d.radical v = false := (p.vertex_color (by omega)).mpr (by decide)
  have hZzQ : Z d.radical z ≤ Q d.radical v := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,
      SimpleGraph.dist_comm,p.dist_end,hpl]
    exact hb2
  have hHZz : H ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    (((critical_Z_commutator_le_moving (h := h) q).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical v)).trans
        ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical v hv)).trans
          (centralizer_le hZzQ))
  apply le_centralizer_iff.mpr
  rw [←hgen]
  exact sup_le (le_centralizer_iff.mp hHT) (le_centralizer_iff.mp hHZz)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

