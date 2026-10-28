module

public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Opposition
public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths.Lines

/-!
# Recovering actual binary Ree lines from opposition

Points and lines are the literal first- and second-parabolic cosets. Every line
has two distinct incident points; its whole point set consists of those two
points and their common point-graph neighbors. The native opposition theorem
therefore sends each actual line to an actual line under any opposition-
preserving point permutation.

Source: the line-reconstruction step of Aschbacher–Smith J.5.7. The separate
identification of all building automorphisms with the full Ree group is not
assumed or asserted here.
-/

public noncomputable section
namespace ReeF4.Octagon.Binary
open Subgroup Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
open SimpleGraph.OctagonShortPaths
local instance lineVertexFintype : Fintype (CosetGeometry.Vertex family) := Fintype.ofFinite _

abbrev LineCoset := Model 0 ⧸ Tits.ExceptionalParabolics.FullRee.second

@[expose] def lineVertex (l : LineCoset) : CosetGeometry.Vertex family := ⟨true,l⟩
@[expose] def pointOnLine (q : PointCoset) (l : LineCoset) : Prop :=
  (graph family).Adj (pointVertex q) (lineVertex l)

theorem pointVertex_injective : Function.Injective pointVertex := by
  intro a b he
  have hh := CosetGeometry.Vertex.mk.inj he
  exact eq_of_heq hh.2

theorem line_incidence_from_adjacency (u v w : PointCoset) (l : LineCoset)
    (hu : pointOnLine u l) (hv : pointOnLine v l) (hne : u≠v) :
    pointOnLine w l ↔ w=u ∨ w=v ∨(pointDistance u w=2 ∧pointDistance v w=2) := by
  have hh := orderTwoFour.line_incidence_iff
    (u:=pointVertex u) (v:=pointVertex v) (w:=pointVertex w) (l:=lineVertex l)
    (by rfl) (by rfl) (by rfl) hu hv (fun he=>hne (pointVertex_injective he))
  simpa only [pointVertex_injective.eq_iff,pointDistance,pointOnLine] using hh

theorem opposition_maps_line (e : PointCoset ≃ PointCoset)
    (hop : ∀ u v,pointDistance (e u) (e v)=8 ↔ pointDistance u v=8)
    (u v : PointCoset) (l : LineCoset)
    (hu : pointOnLine u l) (hv : pointOnLine v l) (hne : u≠v) :
    ∃ l' : LineCoset,∀w,pointOnLine (e w) l' ↔ pointOnLine w l := by
  have hdist : pointDistance u v=2 :=
    distance_two_of_common graph_connected orderTwoFour.cycle_bound
      (fun he=>hne (pointVertex_injective he)) hu hv.symm
  have hdist' := (opposition_determines_adjacency e hop u v).mpr hdist
  obtain ⟨l',⟨hul',hvl'⟩,_⟩ := orderTwoFour.exists_unique_line hdist'
  have ht : l'.type=true := by
    have h := hul'.1
    change false≠l'.type at h
    cases hl : l'.type <;> simp_all
  let L : LineCoset := by
    rcases l' with ⟨b,q⟩
    cases b
    · simp at ht
    · exact q
  have hL : lineVertex L=l' := by
    rcases l' with ⟨b,q⟩
    cases b
    · simp at ht
    · rfl
  have heu : pointOnLine (e u) L := by change (graph family).Adj _ _; rwa [hL]
  have hev : pointOnLine (e v) L := by change (graph family).Adj _ _; rwa [hL]
  refine ⟨L,?_⟩
  intro w
  rw [line_incidence_from_adjacency (e u) (e v) (e w) L heu hev (e.injective.ne hne),
    line_incidence_from_adjacency u v w l hu hv hne,e.injective.eq_iff,e.injective.eq_iff,
    opposition_determines_adjacency e hop,opposition_determines_adjacency e hop]

theorem exists_distinct_points_on_line (l : LineCoset) :
    ∃u v : PointCoset,u≠v ∧pointOnLine u l ∧pointOnLine v l := by
  classical
  let N := (graph family).neighborSet (lineVertex l)
  have hcard : Fintype.card N=3 := by
    rw [←Nat.card_eq_fintype_card]
    exact card_neighbors (lineVertex l)
  obtain ⟨a,b,hab⟩ := Fintype.one_lt_card_iff.mp (show 1<Fintype.card N by omega)
  have toPoint (a : N) : ∃q : PointCoset,pointVertex q=a.val := by
    have ht : a.val.type=false := by
      have hh := a.property.1
      change true≠a.val.type at hh
      cases ha : a.val.type <;> simp_all
    have hz : orderTwoFour.color a.val=0 := by simp [orderTwoFour,coloring,ht]
    obtain ⟨q,hq⟩ := cosetPointEquiv.surjective ⟨a.val,hz⟩
    refine ⟨q,?_⟩
    exact (cosetPointEquiv_val q).symm.trans (congrArg Subtype.val hq)
  obtain ⟨u,hu⟩ := toPoint a
  obtain ⟨v,hv⟩ := toPoint b
  refine ⟨u,v,?_,?_,?_⟩
  · intro he
    apply hab
    apply Subtype.ext
    rw [←hu,←hv,he]
  · change (graph family).Adj _ _
    rw [hu]
    exact a.property.symm
  · change (graph family).Adj _ _
    rw [hv]
    exact b.property.symm

theorem opposition_preserves_lines (e : PointCoset ≃ PointCoset)
    (hop : ∀u v,pointDistance (e u) (e v)=8 ↔pointDistance u v=8)
    (l : LineCoset) : ∃l' : LineCoset,∀w,pointOnLine (e w) l' ↔pointOnLine w l := by
  obtain ⟨u,v,hne,hu,hv⟩ := exists_distinct_points_on_line l
  exact opposition_maps_line e hop u v l hu hv hne

end ReeF4.Octagon.Binary
