module

public import Theory.GroupAction.CubicTree.Tracks
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.Setup
public import Theory.GroupAction.RankTwoCosetGeometry.Kernels

/-!
# Actual translation tracks for the primitive cubic source action

The two index-three local groups contain elements moving the opposite vertex.
Their literal product constructs an embedded integer track through the base
edge. If the chosen movers are involutions, their actions are the two source
reflections. Every track has either its entire line fixed or a finite interval
fixed by any specified set of actors: local finiteness follows from the original
finite endpoints, and the tree hypothesis supplies unique paths.

These are the track-selection and finite-fixed-arc inputs of Goldschmidt
Sections 5--6. They retain the actual coset action, selected local elements and
left-action product convention, without a classification or size hypothesis.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.10)--(2.11),
printed pp.382--383 and the source setup on pp.393--395.
-/

@[expose] public section
open Subgroup Theory.GroupAction.CubicTree SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem trackGraphAction : GraphAction (RankTwo.graph F) G :=
  ⟨fun g _ _ h => (translationGraphIso F g).toHom.map_adj h⟩

private theorem base_fixed {i : Bool} {x : G} (hx : x ∈ F i) :
    x • RankTwo.base F i = RankTwo.base F i := by
  change x ∈ RankTwo.stabilizer F (RankTwo.base F i)
  simpa only [RankTwo.stabilizer, RankTwo.base, stabilizer_base] using hx

private theorem base_moved {i : Bool} {x : G} (hx : x ∉ F i) :
    x • RankTwo.base F i ≠ RankTwo.base F i := by
  intro he
  apply hx
  have hm : x ∈ RankTwo.stabilizer F (RankTwo.base F i) := he
  simpa only [RankTwo.stabilizer, RankTwo.base, stabilizer_base] using hm

/-- The selected local movers give the literal track required in Section 6. -/
def CubicTreeAction.selectedTrack (h : CubicTreeAction F) (x y : G)
    (hx : x ∈ F false) (hy : y ∈ F true)
    (hxb : x ∉ F true) (hya : y ∉ F false) : Track (RankTwo.graph F) G :=
  localMoversTrack h.tree.isAcyclic trackGraphAction
    (a := RankTwo.base F false) (b := RankTwo.base F true) (x := x) (y := y)
    ⟨Bool.false_ne_true, incident_base F false true⟩
    (by exact base_fixed hx) (by exact base_fixed hy)
    (by exact base_moved hxb) (by exact base_moved hya)

@[simp] theorem CubicTreeAction.selectedTrack_zero (h : CubicTreeAction F) (x y : G)
    (hx : x ∈ F false) (hy : y ∈ F true)
    (hxb : x ∉ F true) (hya : y ∉ F false) :
    (h.selectedTrack x y hx hy hxb hya).vertex 0 = RankTwo.base F false :=
  localMoversTrack_zero _ _ _ _ _ _ _

@[simp] theorem CubicTreeAction.selectedTrack_one (h : CubicTreeAction F) (x y : G)
    (hx : x ∈ F false) (hy : y ∈ F true)
    (hxb : x ∉ F true) (hya : y ∉ F false) :
    (h.selectedTrack x y hx hy hxb hya).vertex 1 = RankTwo.base F true :=
  localMoversTrack_one _ _ _ _ _ _ _

@[simp] theorem CubicTreeAction.selectedTrack_translation (h : CubicTreeAction F) (x y : G)
    (hx : x ∈ F false) (hy : y ∈ F true)
    (hxb : x ∉ F true) (hya : y ∉ F false) :
    (h.selectedTrack x y hx hy hxb hya).translation = y*x := rfl

theorem CubicTreeAction.selectedTrack_reflections (h : CubicTreeAction F) (x y : G)
    (hx : x ∈ F false) (hy : y ∈ F true)
    (hxb : x ∉ F true) (hya : y ∉ F false) (hx2 : x*x=1) (hy2 : y*y=1) :
    (∀ i, x • (h.selectedTrack x y hx hy hxb hya).vertex i =
      (h.selectedTrack x y hx hy hxb hya).vertex (-i)) ∧
    (∀ i, y • (h.selectedTrack x y hx hy hxb hya).vertex i =
      (h.selectedTrack x y hx hy hxb hya).vertex (2-i)) :=
  ⟨alternatingVertex_left_reflection (base_fixed hx) (base_fixed hy) hx2 hy2,
    alternatingVertex_right_reflection (base_fixed hx) (base_fixed hy) hx2 hy2⟩

/-- Every track in the original action has the source fixed-interval property. -/
theorem CubicTreeAction.track_fixed_locus (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (U : Set G) :
    t.toLine.fixedIndices U = Set.univ ∨
      ∃ a b : ℤ, t.toLine.fixedIndices U = Set.Icc a b := by
  let : ∀ i, Finite (F i) := h.finite
  exact t.fixedIndices_eq_univ_or_interval h.tree.isAcyclic trackGraphAction
    (fun i => inferInstance) U

theorem CubicTreeAction.exists_local_movers (h : CubicTreeAction F) :
    ∃ x y : G, x ∈ F false ∧ x ∉ F true ∧ y ∈ F true ∧ y ∉ F false := by
  have hl : ∃ x : F false, x ∉ (inclusionAmalgam (F false) (F true)).left.range := by
    by_contra hn
    push Not at hn
    have he := Subgroup.index_eq_one.mpr (show
        (inclusionAmalgam (F false) (F true)).left.range = ⊤ from
      top_unique (fun x _ => hn x))
    have hi := h.primitive.left_index
    omega
  have hr : ∃ y : F true, y ∉ (inclusionAmalgam (F false) (F true)).right.range := by
    by_contra hn
    push Not at hn
    have he := Subgroup.index_eq_one.mpr (show
        (inclusionAmalgam (F false) (F true)).right.range = ⊤ from
      top_unique (fun y _ => hn y))
    have hi := h.primitive.right_index
    omega
  obtain ⟨x, hx⟩ := hl
  obtain ⟨y, hy⟩ := hr
  refine ⟨x, y, x.property, ?_, y.property, ?_⟩
  · intro hxb
    exact hx ⟨⟨x, x.property, hxb⟩, rfl⟩
  · intro hya
    exact hy ⟨⟨y, hya, y.property⟩, rfl⟩

/-- The classification's base edge lies on an actual infinite translation track. -/
theorem CubicTreeAction.exists_track (h : CubicTreeAction F) :
    ∃ t : Track (RankTwo.graph F) G,
      t.vertex 0 = RankTwo.base F false ∧ t.vertex 1 = RankTwo.base F true := by
  obtain ⟨x, y, hx, hxb, hy, hya⟩ := h.exists_local_movers
  exact ⟨h.selectedTrack x y hx hy hxb hya,
    h.selectedTrack_zero x y hx hy hxb hya, h.selectedTrack_one x y hx hy hxb hya⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
