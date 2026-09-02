import Mathlib.GroupTheory.Sylow
universe u v
namespace X
set_option autoImplicit false
structure GD (G : Type u) [Group G] [Finite G] where
  Vertex : Type v
  Gv : Vertex → Subgroup G
  dist : Vertex → Vertex → ℕ
  aa : Vertex
  aa' : Vertex
  bb : ℕ
  critical : dist aa aa' = bb
end X
