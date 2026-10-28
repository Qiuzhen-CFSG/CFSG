module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Stages

/-!
# Centrality at the backward vertex

Once (4.3.6)--(4.3.7) have been proved, noncentrality of R₀ at the vertex
four before the endpoint would make that vertex move relative to the vertex
two before the endpoint. Transport justifies applying the symmetry clause
at the former vertex. The far nonmoving clause then gives a contradiction.

Source: Meierfrankenfeld--Stellmacher (1993), first paragraph of (4.3.8), p.888.
The preceding stages remain explicit premises of this conditional consequence.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geometry : Geometry R}

/-- The first centrality deduction of (4.3.8), with transport at the new
vertex made explicit. It does not assume centrality in its input stages. -/
theorem radius_central_at_four (hb : 0 < geometry.b R) (backward : BackwardFacts geometry)
    (p : Counterexample geometry) (d : Vertex R) (hd : Before p.a p.a' d 4) :
    radiusCommutator p.a p.a' ≤ localCenter d := by
  by_contra h
  have hmove := (backward.backward_bound p d hd h).1
  have hdcolor : color R d = false := (hd.color (by decide)).trans p.end_color
  obtain ⟨q, hqa⟩ := counterexample_at_vertex p hb d hdcolor
  have hsym := backward.moving_symmetric q p.c
  rw [hqa] at hsym
  exact backward.far_not_moving p d hd (hsym.mpr hmove)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation
