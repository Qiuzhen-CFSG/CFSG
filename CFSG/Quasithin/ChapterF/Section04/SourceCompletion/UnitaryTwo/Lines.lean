module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.Quadrangle
public import Theory.Combinatorics.SimpleGraph.QuadrangleCollinearity.Basic
/-!
# Literal lines in the small binary unitary completion

The source metric theorem supplies unique lines and the triangle-on-a-line
property for the original cosets. These statements retain the original
collinearity graph and both endpoint types for subsequent marked recognition.
Source: Aschbacher–Smith F.4.8 andF.4.24, printed pp.278 and287.
-/
public section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Completion
variable {G : Type*} [Group G] [Finite G] (c : Completion G)

omit [Finite G] in
theorem pointGraph_eq_collinearity :
    c.pointGraph = SimpleGraph.QuadrangleCollinearity.graph c.graph (·.type) := rfl

theorem common_line_unique (hcard : Nat.card G = 25920)
    {x y a b : c.Vertex} (hxy : x ≠ y)
    (hxa : c.graph.Adj x a) (hya : c.graph.Adj y a)
    (hxb : c.graph.Adj x b) (hyb : c.graph.Adj y b) : a = b :=
  SimpleGraph.QuadrangleCollinearity.common_vertex_unique (c.quadrangle_metric hcard).1
    hxy hxa hya hxb hyb

theorem collinear_triangle_on_line (hcard : Nat.card G = 25920)
    {x y z a b d : c.Vertex} (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (hxa : c.graph.Adj x a) (hya : c.graph.Adj y a)
    (hxb : c.graph.Adj x b) (hzb : c.graph.Adj z b)
    (hyd : c.graph.Adj y d) (hzd : c.graph.Adj z d) : c.graph.Adj z a :=
  SimpleGraph.QuadrangleCollinearity.triangle_on_line (c.quadrangle_metric hcard).1
    hxy hyz hzx hxa hya hxb hzb hyd hzd
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Completion
