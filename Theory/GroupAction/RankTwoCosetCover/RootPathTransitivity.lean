module
public import Theory.GroupAction.RankTwoCosetCover.PathTransport
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon
/-!
# Rooted path transitivity through a common coset cover

The concrete stabilizer action on nonbacktracking based walks is exactly the
list-action predicate `RootPathTransitive`. Equivariant path lifting therefore
transfers that predicate through two coverings from a common group. Conjugating
a stabilizer extends a rooted assertion to every vertex in the same orbit.

Source: Aschbacher--Smith, F.3.3--4 and F.4.6, printed pp.270 and 276--277.
-/

@[expose] public section
noncomputable section
namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {A B C : Type*} [Group A] [Group B] [Group C]
variable (F : Bool → Subgroup A)

theorem rootPathTransitive_iff (n : ℕ) (v : Vertex F) :
    RootPathTransitive (graph F) A v n ↔
      MulAction.IsPretransitive (stabilizer F v)
        {p : BasedWalk (graph F) n v // p.Nonbacktracking} := by
  constructor
  · intro h
    constructor
    rintro ⟨p, hp⟩ ⟨q, hq⟩
    obtain ⟨a, hav, ha⟩ := h p q hp hq
    refine ⟨⟨a, hav⟩, ?_⟩
    apply Subtype.ext
    apply BasedWalk.vertices_injective n v
    exact (vertices_smul_path F ⟨a, hav⟩ p).trans ha
  · intro h p q hp hq
    obtain ⟨a, ha⟩ := h.exists_smul_eq ⟨p, hp⟩ ⟨q, hq⟩
    refine ⟨a, a.property, ?_⟩
    have hval : a • p = q := congrArg Subtype.val ha
    exact (vertices_smul_path F a p).symm.trans (congrArg BasedWalk.vertices hval)

namespace CoverData
variable {F} {E : Bool → Subgroup B} {D : Bool → Subgroup C}
variable {f : A →* B} {g : A →* C} (c : CoverData F E f) (d : CoverData F D g)
theorem transport_rootPathTransitive (n : ℕ) (v : Vertex F)
    (h : RootPathTransitive (graph E) B (c.vertex v) n) :
    RootPathTransitive (graph D) C (d.vertex v) n :=
  (rootPathTransitive_iff D n (d.vertex v)).mpr
    (c.transport_nbPath_transitive d n v ((rootPathTransitive_iff E n (c.vertex v)).mp h))
end CoverData
end Subgroup.CosetGeometry.RankTwo

namespace SimpleGraph.PathTransitivePolygon
open SimpleGraph
variable {V A : Type*} [Group A] [MulAction A V] {Γ : SimpleGraph V}
variable (h : GraphAction Γ A)
include h

/-- Conjugating the stabilizer transports rooted path transitivity to every
vertex in the same orbit, using the literal action on all path vertices. -/
theorem RootPathTransitive.smul {v : V} {n : ℕ} (ht : RootPathTransitive Γ A v n)
    (g : A) : RootPathTransitive Γ A (g • v) n := by
  intro p q hp hq
  let p' : BasedWalk Γ n v :=
    BasedWalk.rebase (inv_smul_smul g v) (p.map (h.hom g⁻¹))
  let q' : BasedWalk Γ n v :=
    BasedWalk.rebase (inv_smul_smul g v) (q.map (h.hom g⁻¹))
  have hp' : p'.Nonbacktracking := by
    exact (BasedWalk.nonbacktracking_rebase _ _).mpr
      ((h.nonbacktracking_map_iff g⁻¹ p).mpr hp)
  have hq' : q'.Nonbacktracking := by
    exact (BasedWalk.nonbacktracking_rebase _ _).mpr
      ((h.nonbacktracking_map_iff g⁻¹ q).mpr hq)
  obtain ⟨a, hav, ha⟩ := ht p' q' hp' hq'
  refine ⟨g * a * g⁻¹, ?_, ?_⟩
  · simp only [mul_smul, inv_smul_smul, hav]
  · have hpv : p'.vertices = p.vertices.map (g⁻¹ • ·) :=
      (BasedWalk.vertices_rebase (inv_smul_smul g v) _).trans
        (BasedWalk.vertices_map (h.hom g⁻¹) p)
    have hqv : q'.vertices = q.vertices.map (g⁻¹ • ·) :=
      (BasedWalk.vertices_rebase (inv_smul_smul g v) _).trans
        (BasedWalk.vertices_map (h.hom g⁻¹) q)
    have hl := congrArg (List.map (g • ·)) ha
    rw [hpv, hqv] at hl
    simp only [List.map_map, Function.comp_def] at hl
    have hl' : p.vertices.map (fun x => g • a • g⁻¹ • x) =
        q.vertices.map (fun x => g • g⁻¹ • x) := hl
    have he : q.vertices.map (fun x => g • g⁻¹ • x) = q.vertices := by
      calc
        _ = q.vertices.map id := List.map_congr_left (fun x _ => smul_inv_smul g x)
        _ = q.vertices := List.map_id _
    simpa only [mul_smul] using hl'.trans he

end SimpleGraph.PathTransitivePolygon
