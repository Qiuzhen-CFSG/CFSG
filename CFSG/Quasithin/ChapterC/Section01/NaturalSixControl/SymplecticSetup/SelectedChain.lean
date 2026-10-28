module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.SelectedCritical
/-!
# Prescribed backward paths with small critical images

The native backward eligibility theorem constructs a critical path for the
supplied coordinated choice, retaining its first three vertices. At distance
four this path has the original start as midpoint and ends at the original
midpoint. The selected-critical centrality theorem therefore applies using
the original critical path as its actor. Its commutator has order at most two,
and both selected critical images have order two.

The choice object is retained so the selected-kernel argument can consume
this exact image bound. No independent choice, full-X splitting, or radius
central-quotient recognition premise is introduced. The actual characteristic
replacement retains only its separately excluded alternating-block case.

Source: MS93 (5.8), (5.12)(2)--(3), in the native full point-core branch.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- The prescribed backward critical path retains the given coordinated
choice and the literal first three vertices of the selected chain. -/
theorem CoordinatedChoice.exists_prescribed_backward_path
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2<s.geometry.b R) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e}
    (c : s.CoordinatedChoice p (p.walk.getVert 2)) :
    ∃ q : CriticalPath R s.geometry c.alpha1 (p.walk.getVert (p.walk.length-2)),
      q.walk.getVert 1=c.beta1 ∧ q.walk.getVert 2=alpha R ∧
      q.walk.getVert 3=p.walk.getVert 1 := by
  have hi := s.forward_moving_index_two_le h u hfull hb p
  have hc := c.backward_critical_of_eligible s h u hfull hb (by omega)
  let w : (cosetGraph R).Walk c.alpha1 (alpha R) :=
    .cons ((cosetGraph_adj R _ _).mpr c.adjacent_back)
      (.cons ((cosetGraph_adj R _ _).mpr (adjacent_symm R c.adjacent_start)) .nil)
  have hw : w.length=2 := rfl
  let q := p.prepend_two (by omega) c.back_color w hw hc.2
  refine ⟨q,?_,?_,?_⟩
  · simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  · simpa only [SimpleGraph.Walk.getVert_zero] using
      p.prepend_two_overlap (by omega : 2≤s.geometry.b R) c.back_color w hw hc.2
        (i:=0) (by omega)
  · exact p.prepend_two_overlap (by omega : 2≤s.geometry.b R) c.back_color w hw hc.2
      (i:=1) (by have hl := p.length_eq_b; omega)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- At distance four the prescribed backward critical commutator is central
at the original start, and both of its critical images have order two.
All conclusions retain the supplied simultaneous choice. -/
theorem CoordinatedChoice.selected_backward_bounds_of_distance_four
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e}
    (c : s.CoordinatedChoice p (p.walk.getVert 2)) :
    ⁅Z R c.alpha1,Z R (p.walk.getVert (p.walk.length-2))⁆≤
      centralizer (stabilizer R (alpha R):Set (FreeAmalgam R)) ∧
    Nat.card (⁅Z R c.alpha1,Z R (p.walk.getVert (p.walk.length-2))⁆:
      Subgroup (FreeAmalgam R))≤2 ∧
    (Q R (p.walk.getVert (p.walk.length-2))).relIndex (Z R c.alpha1)=2 ∧
    (Q R c.alpha1).relIndex (Z R (p.walk.getVert (p.walk.length-2)))=2 := by
  have hb2 : 2<s.geometry.b R := by omega
  obtain ⟨q,hq1,hq2,_⟩ := c.exists_prescribed_backward_path s h u hfull hb2
  have hl : p.walk.length=4 := p.length_eq_b.trans hb
  have hql : q.walk.length=4 := q.length_eq_b.trans hb
  have hm : (cosetGraph R).dist c.alpha1 (alpha R)≤2 := by
    simpa only [hq2] using (q.dist_start (i:=2) (by omega)).le
  have hc : (cosetGraph R).dist (p.walk.getVert (p.walk.length-2)) (alpha R)≤2 := by
    have hh := (p.dist_start (i:=p.walk.length-2) (Nat.sub_le _ _)).le
    simpa only [SimpleGraph.dist_comm,hl,Nat.reduceSub] using hh
  have hce : (cosetGraph R).dist (p.walk.getVert (p.walk.length-2)) e<s.geometry.b R := by
    rw [p.dist_end,hl,hb]
    decide
  have hgen : Q R (q.walk.getVert 1)⊔Z R e=stabilizer R (alpha R) := by
    rw [hq1]
    simpa only [s.selectedCriticalLayer_eq h u hfull p] using c.generation
  exact ⟨s.selected_critical_commutator_central h u hfull hb2 q p hm hc hce hgen,
    s.selected_critical_commutator_card_le_two h u hfull hb2 q p hm hc hce hgen,
    s.selected_critical_indices_eq_two h u hfull hb2 q p hm hc hce hgen⟩

/-- The supplied selected backward image is small, with no additional
centrality, normalization or quotient-recognition premise. -/
theorem CoordinatedChoice.backward_image_lt_four_of_distance_four
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e}
    (c : s.CoordinatedChoice p (p.walk.getVert 2)) :
    (Q R (p.walk.getVert (p.walk.length-2))).relIndex (Z R c.alpha1)<4 := by
  rw [(c.selected_backward_bounds_of_distance_four s h u hfull hb).2.2.1]
  decide
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B:Subgroup K)

/-- The actual replacement supplies the prescribed path with both critical
images of order two, retaining its original coordinated choice. -/
theorem reducedSource_block_or_prescribed_small_backward_path
    (r : CharacteristicReduction (L.subgroupOf J) (d.B.subgroupOf J))
    (hb : ((originalSource d hm).reduce r).geometry.b r.radical=4)
    {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (c : ((originalSource d hm).reduce r).CoordinatedChoice p (p.walk.getVert 2)) :
    IsAlternatingBlock L 6 ∨
    ∃ q : CriticalPath r.radical ((originalSource d hm).reduce r).geometry
        c.alpha1 (p.walk.getVert (p.walk.length-2)),
      q.walk.getVert 1=c.beta1 ∧ q.walk.getVert 2=alpha r.radical ∧
      q.walk.getVert 3=p.walk.getVert 1 ∧
      (Q r.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z r.radical c.alpha1)=2 ∧
      (Q r.radical c.alpha1).relIndex (Z r.radical (p.walk.getVert (p.walk.length-2)))=2 := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    have h := reduced_nativeCentralLayer d hm r
    obtain ⟨q,hq1,hq2,hq3⟩ := c.exists_prescribed_backward_path s h _ hf (by omega)
    exact ⟨q,hq1,hq2,hq3,(c.selected_backward_bounds_of_distance_four s h _ hf hb).2.2⟩
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
