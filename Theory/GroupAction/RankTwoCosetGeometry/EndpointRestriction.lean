module
public import Theory.GroupAction.RankTwoCosetGeometry.ExtensionGeometry

/-!
# Restricting rooted path actions to an endpoint-containing image

A homomorphism with the prescribed parabolic preimages induces an injective
map of typed coset graphs. Every actor fixing the target root lies in its
parabolic. If that parabolic lies in the image, the actor lifts, and rooted
path transitivity restricts without a global generation hypothesis.

Application: source F.4.6 path transfer for an extension whose native
parabolic generation has not been separately established.
-/

@[expose] public noncomputable section
namespace Subgroup.CosetGeometry.RankTwo.ExtensionGeometry
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {A B : Type*} [Group A] [Group B]
variable (P : Bool → Subgroup A) (Q : Bool → Subgroup B) (f : A →* B)
variable (hpre : ∀ i, (Q i).comap f = P i)

theorem vertex_injective : Function.Injective (vertex P Q f hpre) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  have ht := congrArg (fun v : Vertex Q => v.type) he
  change i = j at ht
  subst j
  have hc : coset P Q f hpre i x = coset P Q f hpre i y := by
    simpa only [vertex, CosetGeometry.Vertex.mk.injEq, heq_eq_eq, true_and] using he
  exact congrArg (CosetGeometry.Vertex.mk i) (coset_injective P Q f hpre i hc)

def graphHom : graph P →g graph Q where
  toFun := vertex P Q f hpre
  map_rel' := by
    rintro v w ⟨ht,a,hv,hw⟩
    exact ⟨ht,f a,congrArg (coset P Q f hpre v.type) hv,
      congrArg (coset P Q f hpre w.type) hw⟩

include hpre

/-- Rooted path transitivity restricts to a subgroup containing the root
endpoint; no global generation or surjectivity is required. -/
theorem rootPathTransitive_of_range (i : Bool) (n : ℕ)
    (hrange : Q i ≤ f.range)
    (ht : RootPathTransitive (graph Q) B (base Q i) n) :
    RootPathTransitive (graph P) A (base P i) n := by
  have hi := vertex_injective P Q f hpre
  let e := graphHom P Q f hpre
  have hb : e (base P i) = base Q i := vertex_base P Q f hpre i
  have ht' : RootPathTransitive (graph Q) B (e (base P i)) n := hb.symm ▸ ht
  intro p q hp hq
  have hinj (v : Vertex P) : Function.Injective (e.mapNeighborSet v) := by
    intro a b hab
    exact Subtype.ext (hi (congrArg Subtype.val hab))
  obtain ⟨b,hbfix,hbpaths⟩ := ht' (p.map e) (q.map e)
    ((BasedWalk.nonbacktracking_map_iff e hinj p).mpr hp)
    ((BasedWalk.nonbacktracking_map_iff e hinj q).mpr hq)
  have hbi : b ∈ Q i := by
    have hh : b ∈ MulAction.stabilizer B (base Q i) := by
      change b • base Q i = base Q i
      simpa only [hb] using hbfix
    rwa [CosetGeometry.stabilizer_base] at hh
  obtain ⟨a,ha⟩ := hrange hbi
  refine ⟨a,hi ?_,?_⟩
  · rw [vertex_smul,ha]
    exact hbfix
  · apply List.map_injective_iff.mpr hi
    rw [List.map_map]
    simp only [BasedWalk.vertices_map,List.map_map] at hbpaths
    exact (List.map_congr_left (fun x _ => (vertex_smul P Q f hpre a x).trans
      (by change f a • vertex P Q f hpre x = b • vertex P Q f hpre x; rw [ha]))).trans hbpaths
end Subgroup.CosetGeometry.RankTwo.ExtensionGeometry
