module
public import Theory.GroupAction.RankTwoCosetGeometry.EvenPathKernels
/-!
# The middle kernel in a four-edge walk

The second-ball kernel at the middle of a four-edge walk fixes its entire
vertex list. Relative normality in the middle vertex stabilizer restricts
to the pointwise path fixer. Neither the graph nor the ambient group needs
to be finite, and backtracking is allowed for these containment facts.

The original cubic--quintic application counts this kernel inside the
four-path fixer. Source: the path and ball-kernel conventions in
Aschbacher--Smith F.3.2--4 and F.7.3, pp.270,311--312.
-/

public section
namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- The radius-two kernel at the middle fixes a four-edge walk pointwise. -/
theorem middle_ballKernel_le_four_path_stabilizer {a : Vertex F}
    (p : BasedWalk (graph F) 4 a) :
    ballKernel F (p.2.1 : Vertex F) 2 ≤ pathStabilizer F p := by
  rcases p with ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,⟨⟨d,hcd⟩,⟨⟨e,hde⟩,pend⟩⟩⟩⟩
  intro g hg
  have hb := ballKernel_succ_le F hbc.symm 1 hg
  have hd := ballKernel_succ_le F hcd 1 hg
  change ∀ z ∈ [a,b,c,d,e], g • z = z
  simp only [List.forall_mem_cons]
  exact ⟨hb _ ((mem_ball_one F _ _).mpr (.inl hab.symm)),
    hb _ (center_mem_ball F b 1), hg _ (center_mem_ball F c 2),
    hd _ (center_mem_ball F d 1), hd _ ((mem_ball_one F _ _).mpr (.inl hde)),
    by intro z hz; cases hz⟩

/-- The middle second-ball kernel is normal in the pointwise four-path fixer. -/
theorem middle_ballKernel_normal_four_path_stabilizer {a : Vertex F}
    (p : BasedWalk (graph F) 4 a) :
    ((ballKernel F (p.2.1 : Vertex F) 2).subgroupOf (pathStabilizer F p)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  apply le_trans ?_ (stabilizer_le_normalizer_ballKernel F (p.2.1 : Vertex F) 2)
  intro g hg
  exact hg _ (by
    change (p.2.1 : Vertex F) ∈ a :: (p.1 : Vertex F) :: p.2.2.vertices
    simp only [List.mem_cons]
    exact Or.inr (Or.inr (origin_mem_vertices F p.2.2)))
end Subgroup.CosetGeometry.RankTwo
