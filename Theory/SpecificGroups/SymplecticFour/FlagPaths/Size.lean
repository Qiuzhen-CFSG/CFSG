module
public import Theory.SpecificGroups.SymplecticFour.FlagPaths.Counts
/-!
# Size of the symplectic flag geometry

Dividing the actual Sp₄ order by either full parabolic order gives
(q + 1)(q² + 1) vertices of each type. The two type fibers are disjoint,
so the entire flag graph has 2(q + 1)(q² + 1) vertices. This is the native
size used with the full extension bound in Aschbacher–Smith F.4.24, p.287.
-/

@[expose] public noncomputable section
open Subgroup Subgroup.CosetGeometry.RankTwo
namespace Theory.SpecificGroups.SymplecticFour.FlagPaths
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
private theorem sq_sub_one (a : ℕ) (ha : 1 ≤ a) : a^2 - 1 = (a-1)*(a+1) := by
  have hh := Nat.sub_add_cancel ha
  have he : (a-1)*(a+1)+1=a^2 := by nlinarith
  omega

theorem index_endpoint (i : Bool) : (family (F := F) i).index =
    (Nat.card F + 1) * (Nat.card F ^ 2 + 1) := by
  have hq := Finite.one_lt_card (α := F)
  have hq1 : 1 ≤ Nat.card F := by omega
  have hq2 : 1 ≤ Nat.card F ^ 2 := one_le_pow₀ hq1
  have hfour : Nat.card F ^ 4 - 1 =
      (Nat.card F - 1) * (Nat.card F + 1) * (Nat.card F ^ 2 + 1) := by
    rw [show Nat.card F ^ 4 = (Nat.card F ^ 2)^2 by ring,
      sq_sub_one _ hq2, sq_sub_one _ hq1]
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := family (F := F) i))
  rw [Subgroup.card_mul_index, card_sp, card_endpoint, hfour, sq_sub_one _ hq1]
  ring

theorem card_vertices : Nat.card (Vertex (family (F := F))) =
    2 * (Nat.card F + 1) * (Nat.card F ^ 2 + 1) := by
  rw [Nat.card_congr (vertexEquivSum (family (F := F))), Nat.card_sum,
    ← Subgroup.index_eq_card, ← Subgroup.index_eq_card, index_endpoint, index_endpoint]
  ring
end Theory.SpecificGroups.SymplecticFour.FlagPaths
