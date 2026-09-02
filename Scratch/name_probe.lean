import Mathlib.GroupTheory.Sylow
universe u v
namespace X
set_option autoImplicit false
structure GD (G : Type u) [Group G] [Finite G] where
  Vertex : Type v
  dist : Vertex → Vertex → ℕ
  a : Vertex
  a' : Vertex
  b : ℕ
  critical : dist a a' = b
end X
