module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.OppositeEdges
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.OppositeNoncentral

/-!
# Exclusion of a strict generated mixed path

For a path whose interior edge kernels generate the midpoint stabilizer,
the full failure commutator is fixed at that midpoint. The marked source pair
ensures one of the two endpoint orientations fails normalization. In either
orientation the full failure line contradicts predecessor-kernel noncentrality.

The generation condition is a geometric selection hypothesis; the separate
forward-selection module constructs such a path from an actual strict slice.
Source: MS93 (5.12)(3), printed pp.926--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- A strict mixed critical path with the retained interior edge generation
is impossible. Both failure orientations use their whole backward kernels. -/
theorem strict_generated_path_false_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 3) =
      stabilizer d.radical (p.walk.getVert 2)) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨q,x,hxL,_,hend,hkernel,hmark,_⟩ :=
    strict_selected_marked_residual_pair_knownSimple hb u him p hstrict
  have hx := Ltilde_le_stabilizer (alpha d.radical) hxL
  have hxa : act d.radical x (alpha d.radical) = alpha d.radical := hx
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.path.walk.length = 4 := q.path.length_eq_b.trans hb
  have hq2 : q.path.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have hnear : (cosetGraph d.radical).dist q.start (alpha d.radical) ≤ 2 := by
    simpa only [hq2] using (q.path.dist_start (i := 2) (by omega)).le
  by_cases hbad : ¬ Z d.radical z ≤ normalizer
      (((Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set _)
  · obtain ⟨hcard,hedge,hfixa,_⟩ :=
      mixed_backward_failure_line_knownSimple hb u him p q hstrict hbad
    have hfixmid := backward_failure_line_midpoint_fixed_knownSimple hb u him p
      q.path.start_color hnear hstrict hgen hbad
    have hh := conjugate_failure_line_not_fixed_knownSimple (e := e) (hz := hz) (hn := hn)
      hb p q 1 ((stabilizer d.radical (alpha d.radical)).one_mem)
    simp only [act_one] at hh
    exact hh hcard hedge hfixa hfixmid
  · have hnorm := Classical.not_not.mp hbad
    have hbadx : ¬ Z d.radical (act d.radical x z) ≤ normalizer
        (((Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2))) ⊔
          Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set _) := by
      intro hh
      exact paired_normalization_false_knownSimple hb u him p q hstrict x hend hnorm
        (backward_kernel_normalization_transfer_knownSimple hb u him p q _ _
          (le_inf inf_le_left hkernel) inf_le_left (le_sup_right.trans_eq hend) hh)
    have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
      apply (cosetGraph_adj d.radical _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using
        p.walk.adj_getVert_succ (i := 0) (by omega)
    have hvt : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
      adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
        (p.walk.adj_getVert_succ (i := 1) (by omega)))
    let s := fullSymmetricAction_knownSimple h e hz hn d hb2
    have hf : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
      rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    have hinter := mixed_strict_seed_intersection_eq_edge s hb2 u hf
      p.start_color hat hvt hstrict
    rw [hinter] at hmark
    obtain ⟨hcard,hedge,hfixa,_⟩ :=
      conjugate_failure_line_fixed_knownSimple hb u him p q hstrict x hx hmark hbadx
    have hsx : 2 < (B d.radical (act d.radical x (alpha d.radical))
        ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical ((p.act x).walk.getVert 2)) := by
      simp only [CriticalPath.act,actWalk_getVert]
      rw [Escape.PairingControl.FirstPairing.B_act hb2 _ _ p.start_color,
        U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
      exact hstrict
    have hgenx : Q d.radical ((p.act x).walk.getVert 1) ⊔
        Q d.radical ((p.act x).walk.getVert 3) =
        stabilizer d.radical ((p.act x).walk.getVert 2) := by
      simp only [CriticalPath.act,actWalk_getVert,Q_act,stabilizer_act,←Subgroup.map_sup,hgen]
    have hnearx : (cosetGraph d.radical).dist q.start (act d.radical x (alpha d.radical)) ≤ 2 := by
      rwa [hxa]
    have hm := backward_failure_line_midpoint_fixed_knownSimple hb u him (p.act x)
      q.path.start_color hnearx hsx hgenx
    simp only [CriticalPath.act,actWalk_getVert,hxa] at hm
    exact conjugate_failure_line_not_fixed_knownSimple (e := e) (hz := hz) (hn := hn)
      hb p q x hx hcard hedge hfixa (hm hbadx)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
