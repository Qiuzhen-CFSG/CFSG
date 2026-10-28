module
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathRootCover
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.Walks

/-!
# Exact transport of ball kernels through a coset covering

Local injectivity lifts fixation of a neighboring vertex once its predecessor
is fixed. Path lifting shows that ball fixation descends through the literal
group map. Together with fixation lifting and the stabilizer isomorphism,
this gives equality of the images of the full ball kernels at every radius.
No global injectivity is required.

The six-path source consumer uses neighbor fixation to recover the chosen
reflection's outer-vertex fixation from its original two-core placement,
and transports the resulting second-ball correction word back to the
reduced graph. Source: DGS, Groups and Graphs (1985), (14.17), p.223;
Aschbacher--Smith F.3.3, p.270.
-/

public section
open SimpleGraph
namespace Subgroup.CosetGeometry.RankTwo.CoverData
variable {X Y : Type*} [Group X] [Group Y]
  {F : Bool → Subgroup X} {E : Bool → Subgroup Y} {f : X →* Y}
  (c : CoverData F E f)

/-- Fixation lifts across one edge from the already fixed starting vertex. -/
theorem fixes_neighbor_of_image {v w : Vertex F} (hvw : (graph F).Adj v w)
    (x : X) (hv : x • v=v) (hw : f x • c.vertex w=c.vertex w) : x • w=w := by
  have ha : (graph F).Adj v (x • w) := by
    have ha := (translationGraphIso F x).toHom.map_adj hvw
    change (graph F).Adj (x • v) (x • w) at ha
    simpa only [hv] using ha
  have he := (c.neighbor_bijective v).1
    (a₁ := ⟨x • w,ha⟩) (a₂ := ⟨w,hvw⟩) (Subtype.ext (by
      change c.vertex (x • w)=c.vertex w
      rw [c.vertex_smul,hw]))
  exact congrArg Subtype.val he

/-- Every ball-fixing element fixes the full target ball. -/
theorem ballKernel_map_le (v : Vertex F) (n : ℕ) :
    (ballKernel F v n).map f ≤ ballKernel E (c.vertex v) n := by
  rintro _ ⟨x,hx,rfl⟩ z hz
  change (graph E).edist (c.vertex v) z≤(n:ℕ∞) at hz
  obtain ⟨p,hp⟩ := exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (by simp) hz)
  obtain ⟨q,hq⟩ := (c.pathEquiv p.length v).surjective (BasedWalk.ofWalk p)
  have hend : c.vertex q.endpoint=z := by
    have he := congrArg BasedWalk.endpoint hq
    rw [c.pathEquiv_apply,BasedWalk.endpoint_ofWalk] at he
    exact (BasedWalk.endpoint_map c.hom q).symm.trans he
  have hqdist : q.endpoint∈ball F v n := by
    change (graph F).edist v q.endpoint≤(n:ℕ∞)
    exact q.toWalk.edist_le.trans (by rw [BasedWalk.length_toWalk,hp]; exact hz)
  rw [←hend,←c.vertex_smul,hx q.endpoint hqdist]

/-- The original group map carries each full ball kernel onto its counterpart. -/
theorem ballKernel_map (v : Vertex F) (n : ℕ) :
    (ballKernel F v n).map f = ballKernel E (c.vertex v) n := by
  apply le_antisymm (c.ballKernel_map_le v n)
  intro y hy
  have hys : y∈stabilizer E (c.vertex v) := ballKernel_le_stabilizer E _ n hy
  obtain ⟨x,hx⟩ := (c.stabilizerHom_bijective v).2 ⟨y,hys⟩
  have he : f x=y := congrArg Subtype.val hx
  exact ⟨x,c.ballKernel_lift v n x x.property (he.symm ▸ hy),he⟩

end Subgroup.CosetGeometry.RankTwo.CoverData
