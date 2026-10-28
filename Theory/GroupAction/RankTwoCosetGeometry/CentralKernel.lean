module

public import Theory.GroupAction.RankTwoCosetGeometry.Kernels
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Central subgroups and the opposite ball kernel

A subgroup fixing a ball at one endpoint fixes the next larger ball at
the other endpoint if that endpoint contains and centralizes it. Local
transitivity supplies the same fixed ball at every neighbor. Conversely,
the opposite endpoint's normal closure fixes the ball of one smaller radius.
The ambient group need not be finite.

Source: the coset-graph argument in Aschbacher--Smith F.7.10--11,
printed pp.313--314.
-/

public section
open Subgroup
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- Centralization extends the fixed radius across the original edge. -/
theorem central_subgroup_le_opposite_ballKernel
    (hgen : F false ⊔ F true = ⊤) (Z : Subgroup G) (n : ℕ)
    (hZ : Z ≤ ballKernel F (base F false) n)
    (htrue : Z ≤ F true) (hc : F true ≤ centralizer (Z : Set G)) :
    Z ≤ ballKernel F (base F true) (n + 1) := by
  have hneighbor (w : Vertex F) (hw : (graph F).Adj (base F true) w) :
      Z ≤ ballKernel F w n := by
    obtain ⟨g,hg,he⟩ := locally_transitive F
      (show (graph F).Adj (base F true) (base F false) from
        ⟨by change true ≠ false; decide,incident_base F true false⟩) hw
    have hg' : g ∈ F true := by
      simpa only [stabilizer,stabilizer_base] using hg
    rw [←he,ballKernel_translate]
    intro z hz
    refine ⟨z,hZ hz,?_⟩
    change g * z * g⁻¹ = z
    rw [←mem_centralizer_iff.mp (hc hg') z hz,mul_inv_cancel_right]
  intro z hz v hv
  rw [mem_ball_iff F hgen] at hv
  by_cases he : base F true = v
  · subst v
    change z ∈ stabilizer F (base F true)
    simpa only [stabilizer_base] using htrue hz
  · obtain ⟨p,hp⟩ := (connected F hgen).exists_walk_length_eq_dist (base F true) v
    cases p with
    | nil => exact (he rfl).elim
    | @cons _ w _ hw p =>
      apply hneighbor w hw hz v
      rw [mem_ball_iff F hgen]
      have hd := SimpleGraph.dist_le p
      simp only [SimpleGraph.Walk.length_cons] at hp
      omega

/-- The literal opposite-vertex normal closure fixes one smaller ball. -/
theorem conjugateSpan_le_opposite_ballKernel (V : Subgroup G) (n : ℕ)
    (hV : V ≤ ballKernel F (base F false) (n + 1)) :
    conjugateSpanBy V (F true) ≤ ballKernel F (base F true) n := by
  apply conjugateSpanBy_le
    (hV.trans (ballKernel_succ_le F
      ⟨Bool.false_ne_true,incident_base F false true⟩ n))
  simpa only [stabilizer_base] using
    stabilizer_le_normalizer_ballKernel F (base F true) n

end Subgroup.CosetGeometry.RankTwo
