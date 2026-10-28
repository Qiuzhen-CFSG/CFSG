module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Path

/-!
# The regular path through the center of a critical orbit pair

For c=p[6], d=p[8] and g in G_a, the displayed walk has vertices
`d^g, p[7]^g, c^g, p[5]^g, a, p[5], c, p[7], d`.
If (d^g,d) is critical, its distance eight makes this walk shortest.
The turn at c comes from the supplied source path, the turn at c^g is
its transported inverse, and the middle turn is g itself. Thus (4.4.4)
applies to this actual path without choosing a different source witness.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(ii), p.898,
and the standing regularity convention after (4.4.2), p.893.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement
open PathCentrality
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

private theorem consecutive {a : Vertex R} (p : Higher.SourcePath a) {i : ℕ} (hi : i < 14) :
    (cosetGraph R).Adj (p.walk.getVert i) (p.walk.getVert (i + 1)) :=
  p.walk.adj_getVert_succ (by rw [p.length_eq]; exact hi)

private theorem acted_edge (g : FreeAmalgam R) {x y : Vertex R}
    (h : (cosetGraph R).Adj x y) :
    (cosetGraph R).Adj (act R g x) (act R g y) :=
  (cosetGraph_adj R _ _).mpr ((adjacent_act_iff R g x y).mpr ((cosetGraph_adj R _ _).mp h))

/-- The eight-edge walk d^g,c^g,a,c,d, including its intervening odd vertices. -/
def orbitWalk {a : Vertex R} (p : Higher.SourcePath a) (g : stabilizer R a) :
    (cosetGraph R).Walk (act R g (p.walk.getVert 8)) (p.walk.getVert 8) :=
  .cons (u := act R g (p.walk.getVert 8)) (v := act R g (p.walk.getVert 7)) (by exact acted_edge g (consecutive p (i := 7) (by decide)).symm)
  (.cons (u := act R g (p.walk.getVert 7)) (v := act R g (p.walk.getVert 6)) (by exact acted_edge g (consecutive p (i := 6) (by decide)).symm)
  (.cons (u := act R g (p.walk.getVert 6)) (v := act R g (p.walk.getVert 5)) (by exact acted_edge g (consecutive p (i := 5) (by decide)).symm)
  (.cons (u := act R g (p.walk.getVert 5)) (v := a) (by
    have h := acted_edge (g : FreeAmalgam R) (consecutive p (i := 4) (by decide)).symm
    simpa only [p.center_eq, show act R g a = a from g.property] using h)
  (.cons (u := a) (v := p.walk.getVert 5) (by simpa only [p.center_eq] using consecutive p (i := 4) (by decide))
  (.cons (u := p.walk.getVert 5) (v := p.walk.getVert 6) (by exact consecutive p (i := 5) (by decide))
  (.cons (u := p.walk.getVert 6) (v := p.walk.getVert 7) (by exact consecutive p (i := 6) (by decide))
  (.cons (u := p.walk.getVert 7) (v := p.walk.getVert 8) (by exact consecutive p (i := 7) (by decide)) .nil)))))))

/-- The original critical orbit pair realized by its path through the supplied a. -/
def orbitCriticalPath {a : Vertex R} (p : Higher.SourcePath a) (earlier : Earlier R geometry)
    (g : stabilizer R a)
    (hd : (cosetGraph R).dist (act R g (p.walk.getVert 8)) (p.walk.getVert 8) = 8)
    (hn : ¬ Z R (act R g (p.walk.getVert 8)) ≤ Q R (p.walk.getVert 8)) :
    CriticalPath R geometry (act R g (p.walk.getVert 8)) (p.walk.getVert 8) where
  start_color := (action_preserves_color R g _).trans
    ((RegularPaths.walk_vertex_color p.start_color p.walk (by rw [p.length_eq]; decide)).mpr
      (by decide : Even 8))
  walk := orbitWalk p g
  shortest := hd.symm
  critical := by
    refine ⟨?_, hn⟩
    rw [geometry.distance_constant]
    · exact hd.trans earlier.distance.symm
    · exact (action_preserves_color R g _).trans
        ((RegularPaths.walk_vertex_color p.start_color p.walk
          (by rw [p.length_eq]; decide)).mpr (by decide : Even 8))

/-- The turns are the original turn at c, its transported inverse, and g at a. -/
theorem orbitCriticalPath_regular {a : Vertex R} (p : Higher.SourcePath a)
    (earlier : Earlier R geometry) (g : stabilizer R a) (hd hn) :
    HasTurnConjugators R (orbitCriticalPath p earlier g hd hn) := by
  obtain ⟨t, ht, hta⟩ := p.turns 6 (by decide) (by decide) (by decide)
  change act R t (p.walk.getVert 8) = p.walk.getVert 4 at hta
  rw [p.center_eq] at hta
  have hti : act R t⁻¹ a = p.walk.getVert 8 := by
    have h := congrArg (act R t⁻¹) hta
    simpa only [← act_mul, mul_inv_cancel, act_one] using h.symm
  have hfix : act R g a = a := g.property
  have hfixi : act R (g : FreeAmalgam R)⁻¹ a = a :=
    (stabilizer R a).inv_mem g.property
  intro i hi hi2 hi8
  change i + 2 ≤ 8 at hi8
  have hev := Nat.even_iff.mp hi
  have hcases : i = 2 ∨ i = 4 ∨ i = 6 := by omega
  rcases hcases with rfl | rfl | rfl
  · refine ⟨(g : FreeAmalgam R)⁻¹ * t⁻¹ * g, ?_, ?_⟩
    · change act R ((g : FreeAmalgam R)⁻¹ * t⁻¹ * g)
        (act R g (p.walk.getVert 6)) = act R g (p.walk.getVert 6)
      have htf : act R t⁻¹ (p.walk.getVert 6) = p.walk.getVert 6 :=
        (stabilizer R _).inv_mem ht
      rw [act_mul, act_mul, ← act_mul R (g : FreeAmalgam R), mul_inv_cancel, act_one, htf]
    · change act R ((g : FreeAmalgam R)⁻¹ * t⁻¹ * g) a = act R g (p.walk.getVert 8)
      rw [act_mul, act_mul, hfixi, hti]
  · refine ⟨g, ?_, ?_⟩
    · exact g.property
    · rfl
  · exact ⟨t, ht, hta⟩


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement
