module
public import Theory.GroupAction.RankTwoCosetGeometry.ShortPaths

/-!
# Cubic kernels along even paths

At a cubic vertex, fixing two distinct neighbors fixes the whole star.
Removing two initial edges therefore turns a pointwise path fixer into
an intersection with one radius-one kernel. Iterating gives explicit
intersections for four- and six-edge paths. The graph and ambient group
may be infinite.

The source application is the original cubic--quintic geometry of
Aschbacher--Smith14.2.20--21, pp.988--989. These identities isolate the
subgroups in the remaining even extension steps, with the path conventions
of F.3.2--4, p.270.
-/

public section
namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- Removing the initial two edges leaves one cubic kernel condition. -/
theorem pathStabilizer_two_cons {n : ℕ} {a : Vertex F}
    (p : BasedWalk (graph F) (n + 2) a) (hp : p.Nonbacktracking)
    (hcard : Nat.card ((graph F).neighborSet (p.1 : Vertex F)) = 3) :
    pathStabilizer F p = ballKernel F (p.1 : Vertex F) 1 ⊓ pathStabilizer F p.2.2 := by
  rcases p with ⟨⟨b, hab⟩, ⟨⟨c, hbc⟩, q⟩⟩
  let r : BasedWalk (graph F) 2 a := ⟨⟨b,hab⟩, ⟨⟨c,hbc⟩, PUnit.unit⟩⟩
  have hr : r.Nonbacktracking := ⟨hp.1, trivial⟩
  have he := pathStabilizer_two_eq_ballKernel_one F r hr hcard
  ext g
  change (∀ z ∈ a :: b :: q.vertices, g • z = z) ↔
    g ∈ ballKernel F b 1 ∧ ∀ z ∈ q.vertices, g • z = z
  simp only [List.forall_mem_cons]
  constructor
  · rintro ⟨ha,hb,hq⟩
    refine ⟨he ▸ ?_, hq⟩
    change ∀ z ∈ [a,b,c], g • z = z
    simp only [List.forall_mem_cons]
    exact ⟨ha,hb,hq c (origin_mem_vertices F q), by intro z hz; cases hz⟩
  · rintro ⟨hk,hq⟩
    exact ⟨hk a ((mem_ball_one F b a).mpr (.inl hab.symm)),
      hk b (center_mem_ball F b 1), hq⟩

/-- The two cubic kernels determine the fixer of a four-edge path. -/
theorem pathStabilizer_four_eq_cubic_kernels {a : Vertex F}
    (p : BasedWalk (graph F) 4 a) (hp : p.Nonbacktracking)
    (hb : Nat.card ((graph F).neighborSet (p.1 : Vertex F)) = 3)
    (hd : Nat.card ((graph F).neighborSet (p.2.2.1 : Vertex F)) = 3) :
    pathStabilizer F p = ballKernel F (p.1 : Vertex F) 1 ⊓
      ballKernel F (p.2.2.1 : Vertex F) 1 := by
  rw [pathStabilizer_two_cons F p hp hb,
    pathStabilizer_two_eq_ballKernel_one F p.2.2 hp.2.2 hd]

/-- Three cubic kernels determine the fixer of a six-edge path. -/
theorem pathStabilizer_six_eq_cubic_kernels {a : Vertex F}
    (p : BasedWalk (graph F) 6 a) (hp : p.Nonbacktracking)
    (hb : Nat.card ((graph F).neighborSet (p.1 : Vertex F)) = 3)
    (hd : Nat.card ((graph F).neighborSet (p.2.2.1 : Vertex F)) = 3)
    (hf : Nat.card ((graph F).neighborSet (p.2.2.2.2.1 : Vertex F)) = 3) :
    pathStabilizer F p = ballKernel F (p.1 : Vertex F) 1 ⊓
      (ballKernel F (p.2.2.1 : Vertex F) 1 ⊓
        ballKernel F (p.2.2.2.2.1 : Vertex F) 1) := by
  rw [pathStabilizer_two_cons F p hp hb,
    pathStabilizer_four_eq_cubic_kernels F p.2.2 hp.2.2 hd hf]
end Subgroup.CosetGeometry.RankTwo
