module
import Mathlib.GroupTheory.Sylow
universe u v
structure C (G : Type u) [Group G] (S : Subgroup G) : Type (max u v + 1) where
  Vertex : Type v
  [f : Finite Vertex]
  x : G → Vertex
namespace C
instance {G : Type u} [Group G] {S : Subgroup G} (c : C G S) : Finite c.Vertex := c.f
end C
