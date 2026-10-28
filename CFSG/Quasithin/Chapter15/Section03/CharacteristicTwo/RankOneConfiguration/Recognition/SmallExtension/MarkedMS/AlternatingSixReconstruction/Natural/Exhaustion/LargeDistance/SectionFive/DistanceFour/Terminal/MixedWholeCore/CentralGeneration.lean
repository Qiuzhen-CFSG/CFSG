module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.ConjugateKernel

/-!
# Central generation forced by the strict mixed branch

The paired full-kernel obstruction supplies a failed normalization in one
of the two actual endpoint orientations. Both endpoints remain on a
critical path, and the backward seed remains within distance two of the
same starting vertex. The source small-kernel argument therefore forces
central generation of the full omega layer at every component vertex.

This removes a genuine structural premise from later marked-conjugator
calculations; it does not assert the mixed terminal contradiction.
Source: MS93 (3.3)(ii), (5.12)(1),(3), printed pp.866--867,924--927.
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


include e hz hn in
/-- The literal strict mixed branch forces full omega central generation,
including the central attachments, in either failed endpoint orientation. -/
theorem strict_omega_centrally_generated_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∀ v : Vertex d.radical, color d.radical v = false →
      X d.radical v = U d.radical v ⊔
        (X d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))) := by
  obtain ⟨q,x,hx,_,_,_,hbad⟩ :=
    strict_conjugate_kernel_failure_knownSimple hb u him p hstrict
  have hq2 : q.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have hql : q.path.walk.length = 4 := q.path.length_eq_b.trans hb
  have hnear : (cosetGraph d.radical).dist q.start a ≤ 2 := by
    simpa only [hq2] using (q.path.dist_start (i := 2) (by omega)).le
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  rcases hbad with hbad | hbad
  · exact (small_backward_kernel_normalized_or_centrally_generated s hc hb p
      (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p)
      q.path.start_color hnear).resolve_left hbad
  · have hxa : act d.radical x a = a := hx
    have hnearx : (cosetGraph d.radical).dist q.start (act d.radical x a) ≤ 2 := by
      rwa [hxa]
    have hh := small_backward_kernel_normalized_or_centrally_generated s hc hb (p.act x)
      (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb (p.act x))
      q.path.start_color hnearx
    simp only [CriticalPath.act,actWalk_getVert,hxa] at hh
    exact hh.resolve_left hbad

include e hz hn in
/-- The forced graph splitting at the base vertex is the literal splitting
of the original overgroup's complete core omega center. -/
theorem strict_original_omega_centrally_generated_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    omegaCenter (pCore 2 d.overgroup) = replacementMoved d ⊔
      (omegaCenter (pCore 2 d.overgroup) ⊓ center d.overgroup) := by
  have hgen := strict_omega_centrally_generated_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u him p hstrict (alpha d.radical) rfl
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let i := embedM d.radical
  have hX : (omegaCenter (pCore 2 d.overgroup)).map i = X d.radical (alpha d.radical) := by
    rw [←omegaCenter_map _ _ (embedM_injective d.radical),
      ←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    rfl
  apply map_injective (embedM_injective d.radical)
  rw [Subgroup.map_sup,hX,←hc.U_eq_moved]
  have hC : (omegaCenter (pCore 2 d.overgroup) ⊓ center d.overgroup).map i =
      X d.radical (alpha d.radical) ⊓
        centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
    rw [←centralizer_univ,←coe_top,
      ←map_inf_centralizer_of_injective i (embedM_injective d.radical),hX,
      ←MonoidHom.range_eq_map]
    change _ ⊓ centralizer ((embedM d.radical).range : Set (FreeAmalgam d.radical)) = _
    exact congrArg (fun T : Subgroup (FreeAmalgam d.radical) =>
      X d.radical (alpha d.radical) ⊓ centralizer (T : Set (FreeAmalgam d.radical)))
      (stabilizer_m_base d.radical).symm
  rw [hC]
  exact hgen

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
