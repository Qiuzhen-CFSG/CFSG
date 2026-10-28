module

public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.Faithfulness
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Lines

/-!
# The full binary Ree group from its opposition action

An opposition-preserving permutation of the original Suzuki-parabolic point
cosets permutes actual lines, since opposition recovers point adjacency and
line incidence. The line permutation is uniquely determined by incidence and
is bijective using the inverse point permutation. This gives a building
automorphism, hence a unique Model0 left translation. The final statement
retains the literal point cosets and their canonical quotient action.

Source: Aschbacher--Smith J.5.6--7, printed pp.447--448.
-/

public section
noncomputable section
namespace ReeF4.Octagon.Binary.Automorphisms
open Subgroup SimpleGraph.OctagonShortPaths
open Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
attribute [local instance] FiniteBridge.pointAction FiniteBridge.lineAction
local instance : Fintype (CosetGeometry.Vertex family) := Fintype.ofFinite _

private theorem lineVertex_injective : Function.Injective lineVertex := by
  intro a b he
  exact eq_of_heq (CosetGeometry.Vertex.mk.inj he).2

/-- A line is determined by its actual incident point cosets. -/
theorem line_eq_of_incidence (l k : LineCoset)
    (h : ∀q,pointOnLine q l ↔ pointOnLine q k) : l=k := by
  obtain ⟨u,v,hne,hu,hv⟩ := exists_distinct_points_on_line l
  have hd : pointDistance u v=2 := distance_two_of_common graph_connected
    orderTwoFour.cycle_bound (fun he=>hne (pointVertex_injective he)) hu hv.symm
  obtain ⟨m,_hm,hm⟩ := orderTwoFour.exists_unique_line hd
  apply lineVertex_injective
  exact (hm (lineVertex l) ⟨hu,hv⟩).trans
    (hm (lineVertex k) ⟨(h u).mp hu,(h v).mp hv⟩).symm

variable (e : PointCoset ≃ PointCoset)
    (hop : ∀u v,pointDistance (e u) (e v)=8 ↔pointDistance u v=8)

private def lineMap (l : LineCoset) : LineCoset :=
  Classical.choose (opposition_preserves_lines e hop l)

private theorem lineMap_spec (l : LineCoset) (q : PointCoset) :
    pointOnLine (e q) (lineMap e hop l) ↔ pointOnLine q l :=
  Classical.choose_spec (opposition_preserves_lines e hop l) q

include hop in
private theorem inverse_opposition :
    ∀u v,pointDistance (e.symm u) (e.symm v)=8 ↔pointDistance u v=8 := by
  intro u v
  simpa only [e.apply_symm_apply] using (hop (e.symm u) (e.symm v)).symm

private theorem lineMap_bijective : Function.Bijective (lineMap e hop) := by
  constructor
  · intro l k he
    apply line_eq_of_incidence
    intro q
    exact (lineMap_spec e hop l q).symm.trans
      (by simpa only [he] using lineMap_spec e hop k q)
  · intro k
    obtain ⟨l,hl⟩ := opposition_preserves_lines e.symm (inverse_opposition e hop) k
    refine ⟨l,line_eq_of_incidence _ _ (fun q=>?_)⟩
    simpa only [e.apply_symm_apply] using
      (lineMap_spec e hop l (e.symm q)).trans (hl q)

/-- The uniquely induced permutation of the actual line cosets. -/
def oppositionLineEquiv : LineCoset ≃ LineCoset :=
  Equiv.ofBijective (lineMap e hop) (lineMap_bijective e hop)

theorem oppositionLineEquiv_incidence (q : PointCoset) (l : LineCoset) :
    pointOnLine (e q) (oppositionLineEquiv e hop l) ↔ pointOnLine q l :=
  lineMap_spec e hop l q

private def vertexEquiv : CosetGeometry.Vertex family ≃ CosetGeometry.Vertex family :=
  (CosetGeometry.RankTwo.vertexEquivSum family).trans
    ((Equiv.sumCongr e (oppositionLineEquiv e hop)).trans
      (CosetGeometry.RankTwo.vertexEquivSum family).symm)

/-- An opposition-preserving point permutation extends to the actual incidence graph. -/
def oppositionGraphIso : graph family ≃g graph family where
  __ := vertexEquiv e hop
  map_rel_iff' := by
    rintro ⟨b,u⟩ ⟨c,v⟩
    cases b <;> cases c
    · change (false≠false ∧_) ↔ (false≠false ∧_)
      simp only [ne_eq,not_true_eq_false,false_and]
    · exact oppositionLineEquiv_incidence e hop u v
    · have hh := oppositionLineEquiv_incidence e hop v u
      exact ((graph family).adj_comm _ _).trans
        (hh.trans ((graph family).adj_comm _ _))
    · change (true≠true ∧_) ↔ (true≠true ∧_)
      simp only [ne_eq,not_true_eq_false,false_and]

theorem oppositionGraphIso_point (q : PointCoset) :
    oppositionGraphIso e hop (pointVertex q)=pointVertex (e q) := by
  have hf : (fun t : PointCoset => oppositionGraphIso e hop (pointVertex t)) =
      (fun t => pointVertex (e t)) := funext (fun _ => rfl)
  exact congrFun hf q

include hop in
/-- Source J.5.6: every opposition-preserving permutation of the original
Suzuki-parabolic point cosets is induced by the full binary Ree group. -/
theorem opposition_equiv_eq_left_action : ∃g : Model 0,∀q : PointCoset,e q=g • q := by
  obtain ⟨g,hg⟩ := automorphism_eq_left_action (oppositionGraphIso e hop)
  refine ⟨g,fun q=>?_⟩
  apply pointVertex_injective
  exact hg (pointVertex q)

/-- The natural left action on the original Suzuki-parabolic point cosets is faithful. -/
theorem point_left_action_faithful (g : Model 0)
    (hg : ∀q : PointCoset,g • q=q) : g=1 := by
  have hp : ∀q : PointCoset,g • pointVertex q=pointVertex q := by
    intro q
    change pointVertex (g • q)=pointVertex q
    rw [hg]
  have hl : ∀l : LineCoset,g • lineVertex l=lineVertex l := by
    intro l
    have he : g • l=l := line_eq_of_incidence _ _ (fun q=>by
      change (graph family).Adj (pointVertex q) (g • lineVertex l) ↔ _
      have hh : (graph family).Adj (g • pointVertex q) (g • lineVertex l) ↔
          (graph family).Adj (pointVertex q) (lineVertex l) :=
        (CosetGeometry.translationGraphIso family g).map_rel_iff
      change (graph family).Adj (pointVertex q) (g • lineVertex l) ↔
        (graph family).Adj (pointVertex q) (lineVertex l)
      simpa only [hp q] using hh)
    change lineVertex (g • l)=lineVertex l
    rw [he]
  apply left_action_faithful g
  rintro ⟨b,q⟩
  cases b
  · exact hp q
  · exact hl q

include hop in
/-- Faithful source J.5.6 identification on the literal point-coset action. -/
theorem opposition_equiv_eq_unique_left_action :
    ∃!g : Model 0,∀q : PointCoset,e q=g • q := by
  obtain ⟨g,hg⟩ := opposition_equiv_eq_left_action e hop
  refine ⟨g,hg,?_⟩
  intro h hh
  have he : g⁻¹*h=1 := point_left_action_faithful _ (fun q=>by
    rw [mul_smul,←hh q,hg q,inv_smul_smul])
  exact (inv_mul_eq_one.mp he).symm

end ReeF4.Octagon.Binary.Automorphisms
