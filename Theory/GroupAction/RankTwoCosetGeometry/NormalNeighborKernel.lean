module

public import Theory.GroupAction.RankTwoCosetGeometry.Kernels

/-!
# A normalized edge subgroup fixes the vertex neighborhood

A subgroup contained in both endpoints and normalized by one endpoint
fixes every neighbor of that endpoint. Local transitivity transports each
neighbor to the standard edge, and normalization transports the subgroup
back into the other endpoint. This is the kernel fact used with the actual
critical path in Aschbacher--Smith 14.7.12, printed p.1046.
-/

public section
open Subgroup
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- A normal subgroup of the second endpoint lying in the first endpoint fixes its radius-one ball. -/
theorem le_base_ballKernel_one (N : Subgroup G)
    (h0 : N ≤ F false) (h1 : N ≤ F true)
    (hn : F true ≤ normalizer (N : Set G)) :
    N ≤ ballKernel F (base F true) 1 := by
  intro n hnN v hv
  rcases (mem_ball_one F (base F true) v).mp hv with hv | rfl
  · obtain ⟨g,hg,rfl⟩ := locally_transitive F
      (show (graph F).Adj (base F true) (base F false) from
        ⟨by change true ≠ false; decide,incident_base F true false⟩) hv
    have hg1 : g ∈ F true := by simpa only [stabilizer,base,stabilizer_base] using hg
    have hconj : g⁻¹*n*g ∈ N := by
      simpa using (mem_normalizer_iff.mp (hn (inv_mem hg1)) n).mp hnN
    have hfix : (g⁻¹*n*g) • base F false = base F false := by
      apply MulAction.mem_stabilizer_iff.mp
      simpa only [stabilizer_base] using h0 hconj
    calc
      n • (g • base F false) = g • ((g⁻¹*n*g) • base F false) := by simp [mul_smul]
      _ = g • base F false := congrArg (g • ·) hfix
  · apply MulAction.mem_stabilizer_iff.mp
    simpa only [stabilizer_base] using h1 hnN

end Subgroup.CosetGeometry.RankTwo
