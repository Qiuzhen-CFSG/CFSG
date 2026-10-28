module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Planes
public import Theory.GroupTheory.GraphUniquenessSystem

/-!
# Short octad cycles and the uniqueness-system base interface

Every closed octad walk of length at most four lies in an actual sextet,
including backtracks and repeated vertices. Sextet transitivity moves such
walks into the standard plane. The resulting normal-closure reduction feeds
the actual `GraphUniquenessSystem.System.IsBase` definition.

The native graph's four-generation and containment of the standard plane's
edges in the model local orbit are explicit remaining premises. Neither is
asserted here. The source/model comparison must discharge both before using
recognition.

Source: Aschbacher, *Sporadic Groups* (1994), §33, 38.6–38.7,
Exercise 13.2(2–3), p.210, and §41, pp.219–222.
-/

@[expose] public section
open Sporadic.Mathieu
namespace Sporadic.Mathieu.M24LocalGeometry.OctadGraph
open PairOvergroups SimpleGraph SimpleGraph.WalkClosure

/-- Literal four-generation, in the nonabelian normal closure of closed walks. -/
def FourGenerated : Prop :=
  IsCycleBase (Γ := graph) (fun _ p => p.length ≤ 4)

/-- Closed walks lying in actual sextets. -/
def planeCycles : Cycles graph := fun _ p =>
  ∃ S : Sextet, ∀ O ∈ p.support, OnPlane O S

theorem vertex_in_plane (O : Octad) : ∃ S : Sextet, OnPlane O S := by
  obtain ⟨g, rfl⟩ := vertex_transitive first O
  exact ⟨g • standardSextet, onPlane_smul g
    (standardTrio_on_standardSextet first first_on_standardTrio)⟩

theorem edge_in_plane {O P : Octad} (hOP : graph.Adj O P) :
    ∃ S : Sextet, OnPlane O S ∧ OnPlane P S := by
  obtain ⟨T,hO,hP⟩ := ((adj_iff_common_trio O P).mp hOP).2
  obtain ⟨S,hS⟩ := line_in_plane T
  exact ⟨S,hS O hO,hS P hP⟩

/-- The triangle and quadrangle geometry fills every closed walk of length at most four. -/
theorem shortCycle_in_plane {O : Octad} (p : graph.Walk O O) (hp : p.length ≤ 4) :
    p ∈ planeCycles O := by
  cases p with
  | nil =>
    obtain ⟨S,hS⟩ := vertex_in_plane O
    exact ⟨S, by simpa using hS⟩
  | @cons O P O hOP p =>
    cases p with
    | nil => exact False.elim (hOP.ne rfl)
    | @cons P Q O hPQ p =>
      cases p with
      | nil =>
        obtain ⟨S,hO,hP⟩ := edge_in_plane hOP
        exact ⟨S, by simpa using And.intro hO (And.intro hP hO)⟩
      | @cons Q R O hQR p =>
        cases p with
        | nil =>
          obtain ⟨S,hO,hP,hQ⟩ := triangle_in_plane hOP hPQ hQR
          exact ⟨S, by simpa using And.intro hO (And.intro hP (And.intro hQ hO))⟩
        | cons hRO p =>
          cases p with
          | nil =>
            obtain ⟨S,hO,hP,hQ,hR⟩ := closed_square_in_plane hOP hPQ hQR hRO
            exact ⟨S, by simpa using And.intro hO (And.intro hP (And.intro hQ (And.intro hR hO)))⟩
          | cons h p =>
            simp only [Walk.length_cons] at hp
            omega

/-- The remaining four-generation theorem is precisely what turns short-cycle
coplanarity into a base of plane cycles. -/
theorem planeCycles_isCycleBase_of_fourGenerated (h4 : FourGenerated) :
    IsCycleBase planeCycles := by
  intro O p
  exact (h4 O p).of_generators (fun _ q hq => .cycle q (shortCycle_in_plane q hq))

/-- A literal local edge relation containing the standard plane fills all
plane cycles after translation. -/
theorem planeCycle_in_local_closure (R : Octad → Octad → Prop)
    (hR : ∀ {O P}, graph.Adj O P → OnPlane O standardSextet →
      OnPlane P standardSextet → R O P)
    {O : Octad} (p : graph.Walk O O) (hp : p ∈ planeCycles O) :
    p ∈ closure (fun _ q => ∃ g : M24,
      Supported (fun A B => R (g⁻¹ • A) (g⁻¹ • B)) q) O := by
  obtain ⟨S,hS⟩ := hp
  obtain ⟨g,rfl⟩ := sextet_transitive S
  apply Rel.cycle
  refine ⟨g, ?_⟩
  have hpoint (P : Octad) (hP : P ∈ p.support) : OnPlane (g⁻¹ • P) standardSextet := by
    simpa using onPlane_smul g⁻¹ (hS P hP)
  have aux : ∀ {A B} (q : graph.Walk A B),
      (∀ P ∈ q.support, OnPlane (g⁻¹ • P) standardSextet) →
      Supported (fun A B => R (g⁻¹ • A) (g⁻¹ • B)) q := by
    intro A B q hq
    induction q with
    | nil => trivial
    | cons h q ih =>
      exact ⟨hR (preserves g⁻¹ h) (hq _ (by simp)) (hq _ (by simp)),
        ih (fun P hP => hq P (by simp [hP]))⟩
  exact aux p hpoint

/-- Conditional base reduction retaining the genuine unproved four-generation
premise and the literal standard-plane edge containment. -/
theorem local_isCycleBase_of_fourGenerated (h4 : FourGenerated) (R : Octad → Octad → Prop)
    (hR : ∀ {O P}, graph.Adj O P → OnPlane O standardSextet →
      OnPlane P standardSextet → R O P) :
    IsCycleBase (Γ := graph) (fun _ q => ∃ g : M24,
      Supported (fun A B => R (g⁻¹ • A) (g⁻¹ • B)) q) := by
  intro O p
  exact (planeCycles_isCycleBase_of_fourGenerated h4 O p).of_generators
    (fun _ q hq => planeCycle_in_local_closure R hR q hq)

end Sporadic.Mathieu.M24LocalGeometry.OctadGraph

namespace Theory.GroupTheory.GraphUniquenessSystem.System
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry

/-- Native octad-graph base reduction. Four-generation and local-plane edge
containment remain explicit obligations of the model-system construction. -/
theorem isBase_of_octadGraph_fourGenerated (U : System M24 Octad)
    (hgraph : U.graph = OctadGraph.graph) (h4 : OctadGraph.FourGenerated)
    (hlocal : ∀ {O P}, OctadGraph.graph.Adj O P →
      OctadGraph.OnPlane O standardSextet → OctadGraph.OnPlane P standardSextet →
      U.localEdge O P) : U.IsBase := by
  change SimpleGraph.WalkClosure.IsCycleBase (Γ := U.graph)
    (fun _ p => ∃ g : M24, SimpleGraph.WalkClosure.Supported
      (fun O P => U.localEdge (g⁻¹ • O) (g⁻¹ • P)) p)
  rw [hgraph]
  exact OctadGraph.local_isCycleBase_of_fourGenerated h4 U.localEdge hlocal

end Theory.GroupTheory.GraphUniquenessSystem.System
