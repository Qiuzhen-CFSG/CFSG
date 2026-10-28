module
public import Theory.GroupAction.RankTwoCosetGeometry.Kernels
/-!
# Successive ball kernels as relative normal cores

The radius-(n+1) kernel at a vertex is the normal core, inside its vertex
stabilizer, of the intersection of the radius-n kernels at that vertex and
one neighbor. Local transitivity supplies all neighboring balls, whose union
covers the next ball. No finiteness or tree hypothesis is required.

This gives the normal-subgroup propagation into the third kernel used in
Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985), (12.9), pp.188–189.
-/
public section
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)
/-- Relative normality propagates a neighboring ball constraint to the next radius. -/
theorem ballKernel_succ_eq_normalCore {v w : Vertex F} (h : (graph F).Adj v w) (n : ℕ) :
    (ballKernel F v (n + 1)).subgroupOf (stabilizer F v) =
      ((ballKernel F v n ⊓ ballKernel F w n).subgroupOf (stabilizer F v)).normalCore := by
  apply le_antisymm
  · apply normal_le_normalCore.mpr
    intro x hx
    exact ⟨ballKernel_antitone F v (Nat.le_succ n) hx,
      ballKernel_succ_le F h n hx⟩
  · intro x hx z hz
    have hfix (u : Vertex F) (hu : (graph F).Adj v u) :
        (x:G) ∈ ballKernel F u n := by
      obtain ⟨g,hg,rfl⟩ := locally_transitive F h hu
      have hc := hx (⟨g⁻¹,(stabilizer F v).inv_mem hg⟩ : stabilizer F v)
      have hc' : g⁻¹ * (x:G) * g ∈ ballKernel F w n := by
        have hc2 := hc.2
        change g⁻¹ * (x:G) * (g⁻¹)⁻¹ ∈ ballKernel F w n at hc2
        simpa only [inv_inv] using hc2
      have hh := (conj_mem_ballKernel_iff F g (g⁻¹*(x:G)*g) w n).mpr hc'
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using hh
    have hdist : (graph F).edist v z ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp : ((n + 1 : ℕ) : ℕ∞) ≠ ⊤) hz
    obtain ⟨p,hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hdist
    have hlen : p.length ≤ n + 1 := by
      have hh : (p.length : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞) := hp ▸ hz
      exact ENat.natCast_le_natCast.mp hh
    cases p with
    | nil => exact x.property
    | @cons _ u _ hu p =>
      apply hfix u hu z
      exact p.edist_le.trans (ENat.natCast_le_natCast.mpr (by simpa using hlen))

end Subgroup.CosetGeometry.RankTwo
