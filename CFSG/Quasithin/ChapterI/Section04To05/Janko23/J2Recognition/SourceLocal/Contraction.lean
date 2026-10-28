module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.CommonNeighbors.SL23
public import Theory.GroupTheory.Amalgam.UniquenessSystem.ShortCycles

/-!
# The remaining pentagon obligation for the source graph

The source incidence calculations give diameter two without additional
premises. The general short-cycle criterion therefore reduces source
triangle contraction to connectivity of the nonedge common-neighbor
graphs and contraction of pentagons. Both the A₅ and SL₂(3) connectivity
branches are proved for the arbitrary source group. Only the pentagon
argument of Aschbacher, *Sporadic Groups* (1994), 47.9, pp.265–266,
remains explicit in the final reduction below. The older conditional
interfaces are preserved; unconditional contraction and recognition are
not asserted here.
-/

public section
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The proved source diameter discharges the short-path premise of the
square-and-pentagon criterion. Only the remaining source geometry is assumed. -/
theorem triangleSimplyConnected_of_common_connected_pentagons (D : Seed G)
    (hconn : ∀ A B : D.Vertex, A ≠ B → ¬ D.graph.Adj A B →
      (D.graph.commonNeighborGraph A B).Preconnected)
    (hpentagon : ∀ (A : D.Vertex) (p : D.graph.Walk A A),
      p.length = 5 → p.TriangleHomotopy .nil) : D.graph.TriangleSimplyConnected :=
  SimpleGraph.triangleSimplyConnected_of_common_connected_pentagons
    (EdgeConfigurations.Distances.short_walk D) hconn hpentagon

/-- The A₅ common-neighbor case and suborbit transport are discharged;
only one SL₂(3) pair and the pentagon argument remain. -/
theorem triangleSimplyConnected_of_one_sl2_pentagons (D : Seed G) (Y : D.Vertex)
    (hY : sl2Join D D.base Y)
    (hconn : (D.graph.commonNeighborGraph D.base Y).Preconnected)
    (hpentagon : ∀ (A : D.Vertex) (p : D.graph.Walk A A),
      p.length = 5 → p.TriangleHomotopy .nil) : D.graph.TriangleSimplyConnected :=
  triangleSimplyConnected_of_common_connected_pentagons D
    (CommonNeighbors.connected_of_one_sl2 D Y hY hconn) hpentagon

/-- Source diameter and both nonedge connectivity branches discharge the
short-walk and square premises. Only five-step loops remain to be contracted. -/
theorem triangleSimplyConnected_of_pentagons (D : Seed G)
    (hpentagon : ∀ (A : D.Vertex) (p : D.graph.Walk A A),
      p.length = 5 → p.TriangleHomotopy .nil) : D.graph.TriangleSimplyConnected :=
  triangleSimplyConnected_of_common_connected_pentagons D
    (CommonNeighbors.nonedge_connected D) hpentagon

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
