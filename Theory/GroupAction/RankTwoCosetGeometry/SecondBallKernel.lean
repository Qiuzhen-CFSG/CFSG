module
public import Theory.GroupAction.RankTwoCosetGeometry.Kernels
/-!
# The second ball as a relative normal core

The radius-two kernel at a vertex is the normal core, inside that vertex
stabilizer, of the intersection of the two incident radius-one kernels.
Local transitivity supplies all neighboring stars; their union is the second
ball. The graph and ambient group need not be finite or connected.

The literal quintic application identifies this kernel with the centralizer
of the elementary neighbor span. Source: Aschbacher--Smith F.3.2--4 and
F.7.3, printed pp.270 and311--312.
-/

public section
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- The second ball is controlled by the first balls at its neighbors. -/
theorem ballKernel_two_eq_normalCore {v w : Vertex F} (h : (graph F).Adj v w) :
    (ballKernel F v 2).subgroupOf (stabilizer F v) =
      ((ballKernel F v 1 ⊓ ballKernel F w 1).subgroupOf (stabilizer F v)).normalCore := by
  apply le_antisymm
  · apply normal_le_normalCore.mpr
    intro x hx
    exact ⟨ballKernel_antitone F v (by decide : 1 ≤ 2) hx,
      ballKernel_succ_le F h 1 hx⟩
  · intro x hx z hz
    have hfix (u : Vertex F) (hu : (graph F).Adj v u) :
        (x:G) ∈ ballKernel F u 1 := by
      obtain ⟨g,hg,rfl⟩ := locally_transitive F h hu
      have hc := hx (⟨g⁻¹,(stabilizer F v).inv_mem hg⟩ : stabilizer F v)
      have hc' : g⁻¹ * (x:G) * g ∈ ballKernel F w 1 := by
        have hc2 := hc.2
        change g⁻¹ * (x:G) * (g⁻¹)⁻¹ ∈ ballKernel F w 1 at hc2
        simpa only [inv_inv] using hc2
      have hh := (conj_mem_ballKernel_iff F g (g⁻¹*(x:G)*g) w 1).mpr hc'
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using hh
    have hdist : (graph F).edist v z ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp : (2 : ℕ∞) ≠ ⊤) hz
    obtain ⟨p,hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hdist
    have hlen : p.length ≤ 2 := by
      have hh : (p.length : ℕ∞) ≤ (2 : ℕ∞) := hp ▸ hz
      exact ENat.natCast_le_natCast.mp hh
    cases p with
    | nil => exact x.property
    | @cons _ u _ hu p =>
      apply hfix u hu z
      exact p.edist_le.trans (ENat.natCast_le_natCast.mpr (by simpa using hlen))

/-- The normal core of the incident kernel intersection, in the actual vertex group. -/
theorem base_ballKernel_two (i : Bool) :
    (ballKernel F (base F i) 2).subgroupOf (F i) =
      ((ballKernel F (base F false) 1 ⊓ ballKernel F (base F true) 1).subgroupOf (F i)).normalCore := by
  have hh := ballKernel_two_eq_normalCore F
    (v := base F i) (w := base F (!i))
    ⟨by change i ≠ !i; cases i <;> decide, incident_base F i (!i)⟩
  have hs : stabilizer F (base F i) = F i := Subgroup.CosetGeometry.stabilizer_base F i
  rw [hs] at hh
  cases i <;> simpa only [Bool.not_false, Bool.not_true, inf_comm] using hh
end Subgroup.CosetGeometry.RankTwo
