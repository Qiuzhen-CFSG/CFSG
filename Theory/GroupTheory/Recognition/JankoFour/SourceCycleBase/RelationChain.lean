module

public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Geometry
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Base

/-!
# The AS91 relation filtration and common-neighbor components

The ternary relations are triangles, coplanar two-step paths, those paths
together with native δ₃, and all two-step paths. Their binary relations are
defined by existence of the middle vertex. `commonComponent` uses reachability
in the *induced* common-neighbor graph, not the entire common-neighbor set.

The elementary component move is proved in the existing nonabelian walk
congruence, via its triangle-homotopy adapter. At level zero the source D₀
adds no vertices to the component. The higher contraction conditions and the
minimal-cycle argument of (1.2)–(1.4) are not assumed by `Input`.

Source: Aschbacher–Segev (1991), pp.590–592 and opening of §7, p.603.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase

open SimpleGraph

section Components
variable {V : Type*} (Γ : SimpleGraph V)

/-- CΔ(xuy), including its specified component representative u. -/
def commonComponent (x u y : V) : Set V :=
  {v | ∃ hu : Γ.Adj x u ∧ Γ.Adj y u, ∃ hv : Γ.Adj x v ∧ Γ.Adj y v,
    (Γ.commonNeighborGraph x y).Reachable ⟨u, hu⟩ ⟨v, hv⟩}

theorem commonComponent_subset (x u y : V) :
    commonComponent Γ x u y ⊆ {v | Γ.Adj x v ∧ Γ.Adj y v} := by
  rintro v ⟨_, hv, _⟩
  exact hv

theorem mem_commonComponent_self {x u y : V} (hx : Γ.Adj x u) (hy : Γ.Adj y u) :
    u ∈ commonComponent Γ x u y := ⟨⟨hx, hy⟩, ⟨hx, hy⟩, .refl _⟩

theorem commonComponent_step {x u y v w : V} (hv : v ∈ commonComponent Γ x u y)
    (hw : Γ.Adj x w ∧ Γ.Adj y w) (hvw : Γ.Adj v w) :
    w ∈ commonComponent Γ x u y := by
  obtain ⟨hu, hv, hp⟩ := hv
  have hedge : (Γ.commonNeighborGraph x y).Adj ⟨v, hv⟩ ⟨w, hw⟩ := hvw
  exact ⟨hu, hw, hp.trans ⟨hedge.toWalk⟩⟩

/-- Moving the middle vertex along a common-neighbor component is an actual
normal triangle-walk relation, with both endpoints retained. -/
theorem two_step_related_of_commonComponent {x u y v : V}
    (hxu : Γ.Adj x u) (huy : Γ.Adj u y)
    (hxv : Γ.Adj x v) (hvy : Γ.Adj v y)
    (hv : v ∈ commonComponent Γ x u y) :
    WalkClosure.Rel (WalkClosure.triangles Γ)
      (.cons hxu huy.toWalk) (.cons hxv hvy.toWalk) := by
  obtain ⟨hu, hv, ⟨p⟩⟩ := hv
  have all : ∀ (a b : {w // Γ.Adj x w ∧ Γ.Adj y w})
      (q : (Γ.commonNeighborGraph x y).Walk a b),
      Walk.TriangleHomotopy
        (.cons a.property.1 a.property.2.symm.toWalk)
        (.cons b.property.1 b.property.2.symm.toWalk) := by
    intro a b q
    induction q with
    | nil => exact .refl _
    | @cons a b c hab q ih =>
      have hab' : Γ.Adj a.val b.val := hab
      have ht : Walk.TriangleHomotopy
          (.cons a.property.1 a.property.2.symm.toWalk)
          (.cons b.property.1 b.property.2.symm.toWalk) :=
        (Walk.TriangleHomotopy.cons a.property.1
          (.triangle hab' b.property.2.symm a.property.2.symm .nil)).symm.trans
            (.triangle a.property.1 hab' b.property.1 b.property.2.symm.toWalk)
      exact ht.trans ih
  exact (all ⟨u, hu⟩ ⟨v, hv⟩ p).toCycleRel

end Components

variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

namespace Input
variable (d : Input h)

def coplanarStep (x u y : Point d.P) : Prop :=
  ∃ l k : Line d.L, OnLine d.L u l ∧ OnLine d.L x l ∧
    OnLine d.L u k ∧ OnLine d.L y k ∧ Coplanar d.L l k

def deltaThreeStep (x u y : Point d.P) : Prop :=
  ∃ l k : Line d.L, OnLine d.L u l ∧ OnLine d.L x l ∧
    OnLine d.L u k ∧ OnLine d.L y k ∧ LineType d.residue 3 u l k

def ternary (i : Fin 4) (x u y : Point d.P) : Prop :=
  Adj d.L x u ∧ Adj d.L u y ∧
    match i.val with
    | 0 => Adj d.L x y
    | 1 => d.coplanarStep x u y
    | 2 => d.coplanarStep x u y ∨ d.deltaThreeStep x u y
    | _ => True

/-- The binary relation is exactly existence of a middle vertex. -/
def binary (i : Fin 4) (x y : Point d.P) : Prop := ∃ u, d.ternary i x u y

/-- The literal D_k of Hypothesis B, including the component, not all common neighbors. -/
def neighborhoodExtension (i : Fin 4) (x u y : Point d.P) : Set (Point d.P) :=
  commonComponent (graph d.L) x u y ∪
    {w | Adj d.L x w ∧ ∃ c ∈ commonComponent (graph d.L) x u y, d.ternary i y c w}

theorem coplanarStep_iff_plane {x u y : Point d.P}
    (hxu : Adj d.L x u) (huy : Adj d.L u y) :
    d.coplanarStep x u y ↔ ∃ π, OnPlane d.P x π ∧ OnPlane d.P u π ∧ OnPlane d.P y π := by
  constructor
  · rintro ⟨l, k, hul, hxl, huk, hyk, π, hl, hk⟩
    exact ⟨π, d.string x l π hxl hl, d.string u l π hul hl, d.string y k π hyk hk⟩
  · rintro ⟨π, hx, hu, hy⟩
    obtain ⟨l, ⟨hxl, hul⟩, _⟩ := d.unique_line x u hxu
    obtain ⟨k, ⟨huk, hyk⟩, _⟩ := d.unique_line u y huy
    exact ⟨l, k, hul, hxl, huk, hyk, π,
      d.plane_closed x u l π hxu.1 hxl hul hx hu,
      d.plane_closed u y k π huy.1 huk hyk hu hy⟩

theorem ternary_zero_le_one {x u y : Point d.P} (ht : d.ternary 0 x u y) :
    d.ternary 1 x u y := by
  obtain ⟨π, hx, hu, hy⟩ := d.triangles_in_plane x u y ht.1 ht.2.1 (adj_symm ht.2.2)
  exact ⟨ht.1, ht.2.1, (d.coplanarStep_iff_plane ht.1 ht.2.1).mpr ⟨π, hx, hu, hy⟩⟩

theorem ternary_one_le_two {x u y : Point d.P} (ht : d.ternary 1 x u y) :
    d.ternary 2 x u y := ⟨ht.1, ht.2.1, Or.inl ht.2.2⟩

theorem ternary_two_le_three {x u y : Point d.P} (ht : d.ternary 2 x u y) :
    d.ternary 3 x u y := ⟨ht.1, ht.2.1, trivial⟩

theorem ternary_zero_symm {x u y : Point d.P} (ht : d.ternary 0 x u y) :
    d.ternary 0 y u x := ⟨adj_symm ht.2.1, adj_symm ht.1, adj_symm ht.2.2⟩

theorem ternary_one_symm {x u y : Point d.P} (ht : d.ternary 1 x u y) :
    d.ternary 1 y u x := by
  obtain ⟨π, hx, hu, hy⟩ := (d.coplanarStep_iff_plane ht.1 ht.2.1).mp ht.2.2
  exact ⟨adj_symm ht.2.1, adj_symm ht.1,
    (d.coplanarStep_iff_plane (adj_symm ht.2.1) (adj_symm ht.1)).mpr ⟨π, hy, hu, hx⟩⟩

theorem ternary_three_symm {x u y : Point d.P} (ht : d.ternary 3 x u y) :
    d.ternary 3 y u x := ⟨adj_symm ht.2.1, adj_symm ht.1, trivial⟩

/-- At the bottom level the extra triangle vertices stay in the same component. -/
theorem neighborhoodExtension_zero (x u y : Point d.P) :
    d.neighborhoodExtension 0 x u y = commonComponent (graph d.L) x u y := by
  apply Set.ext
  intro w
  constructor
  · rintro (hw | ⟨hxw, c, hc, ht⟩)
    · exact hw
    · exact commonComponent_step (graph d.L) hc ⟨hxw, ht.2.2⟩ ht.2.1
  · exact Or.inl

theorem neighborhoodExtension_neighbors (i : Fin 4) (x u y : Point d.P) :
    d.neighborhoodExtension i x u y ⊆ {w | Adj d.L x w} := by
  rintro w (hw | hw)
  · exact (commonComponent_subset (graph d.L) x u y hw).1
  · exact hw.1

/-- The inclusion used in (1.3). Adjacent pairs are kept explicitly; this
avoids silently identifying the raw middle-vertex relation with its reflexive
graph closure at the bottom of Hypothesis A. -/
theorem neighborhoodExtension_subset (i : Fin 4) (x u y : Point d.P) :
    d.neighborhoodExtension i x u y ⊆
      {w | Adj d.L x w ∧ (Adj d.L y w ∨ d.binary i y w)} := by
  rintro w (hw | ⟨hxw, c, hc, ht⟩)
  · exact ⟨(commonComponent_subset (graph d.L) x u y hw).1,
      Or.inl (commonComponent_subset (graph d.L) x u y hw).2⟩
  · exact ⟨hxw, Or.inr ⟨c, ht⟩⟩

end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
