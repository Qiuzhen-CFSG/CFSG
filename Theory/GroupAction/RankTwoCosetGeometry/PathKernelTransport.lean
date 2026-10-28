module
public import Theory.GroupAction.RankTwoCosetCover.RootPathTransitivity
public import Theory.GroupAction.RankTwoCosetGeometry.Kernels
/-!
# Conjugating path fixers and ball kernels

A nonbacktracking path based at either vertex type is a translate of one
based at the corresponding standard vertex. Rooted path transitivity
then makes any two such paths translates. Conjugation carries the literal
pointwise fixer and each ball kernel along that same translation.

The cubic--quintic five-path application uses this to transport the middle
kernel condition and propagate a failed endpoint escape. No finiteness
of the ambient group or graph is needed.
Source: the action conventions of Aschbacher--Smith F.3.2--4 and F.7.3,
printed pp.270,311--312.
-/

public section
namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

set_option backward.isDefEq.respectTransparency false in
/-- Every path is a translate of a path at the standard vertex of its type. -/
theorem exists_base_path_translate {n : ℕ} {i : Bool} {a : Vertex F}
    (ha : a.type = i) (q : BasedWalk (graph F) n a) (hq : q.Nonbacktracking) :
    ∃ p : BasedWalk (graph F) n (base F i), p.Nonbacktracking ∧
      ∃ g : G, p.vertices.map (g • ·) = q.vertices := by
  obtain ⟨g,hg⟩ := exists_smul_base F a
  rw [ha] at hg
  have hbase : g⁻¹ • a = base F i := by rw [←hg,inv_smul_smul]
  let p := BasedWalk.rebase hbase (q.map (translationGraphIso F g⁻¹).toHom)
  have hp : p.Nonbacktracking := (BasedWalk.nonbacktracking_rebase _ _).mpr
    ((BasedWalk.nonbacktracking_map_iff (translationGraphIso F g⁻¹).toHom
      (fun v => (translationGraphIso F g⁻¹).mapNeighborSet v |>.injective) q).mpr hq)
  refine ⟨p,hp,g,?_⟩
  rw [show p.vertices = q.vertices.map (g⁻¹ • ·) from by
    exact (BasedWalk.vertices_rebase hbase _).trans
      (BasedWalk.vertices_map (translationGraphIso F g⁻¹).toHom q),List.map_map]
  simp only [Function.comp_def,smul_inv_smul]
  exact List.map_id _

/-- Rooted transitivity aligns paths based anywhere in the same vertex orbit. -/
theorem exists_path_translate_of_rootPathTransitive {n : ℕ} {i : Bool}
    (ht : RootPathTransitive (graph F) G (base F i) n)
    (p : BasedWalk (graph F) n (base F i)) (hp : p.Nonbacktracking)
    {a : Vertex F} (ha : a.type = i) (q : BasedWalk (graph F) n a)
    (hq : q.Nonbacktracking) : ∃ g : G, p.vertices.map (g • ·) = q.vertices := by
  obtain ⟨r,hr,g,hg⟩ := exists_base_path_translate F ha q hq
  obtain ⟨b,_,hb⟩ := ht p r hp hr
  refine ⟨g*b,?_⟩
  simpa only [List.map_map,Function.comp_def,←mul_smul] using
    (congrArg (List.map (g • ·)) hb).trans hg

/-- Translating all path vertices conjugates their pointwise fixer. -/
theorem pathStabilizer_map_conj_of_vertices {n : ℕ} {a b : Vertex F}
    (p : BasedWalk (graph F) n a) (q : BasedWalk (graph F) n b)
    (g : G) (he : p.vertices.map (g • ·) = q.vertices) :
    (pathStabilizer F p).map (MulAut.conj g).toMonoidHom = pathStabilizer F q := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩ z hz
    rw [←he] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    change (g*y*g⁻¹) • (g • w) = g • w
    simp only [mul_smul,inv_smul_smul,hy w hw]
  · intro hx
    refine ⟨g⁻¹*x*g,?_,by simp [MulAut.conj_apply,mul_assoc]⟩
    intro z hz
    have hh := hx (g • z) (he ▸ List.mem_map.mpr ⟨z,hz,rfl⟩)
    simpa only [mul_smul,inv_smul_smul] using congrArg (g⁻¹ • ·) hh

/-- Containment in a ball kernel transports through the same path translation. -/
theorem pathStabilizer_le_ballKernel_of_vertices {n : ℕ} {a b u v : Vertex F}
    (p : BasedWalk (graph F) n a) (q : BasedWalk (graph F) n b)
    (g : G) (he : p.vertices.map (g • ·) = q.vertices)
    (huv : g • u = v) (k : ℕ)
    (hle : pathStabilizer F p ≤ ballKernel F u k) :
    pathStabilizer F q ≤ ballKernel F v k := by
  rw [←pathStabilizer_map_conj_of_vertices F p q g he,←huv,ballKernel_translate]
  exact map_mono hle

/-- Endpoint-kernel containment is invariant under path translation. -/
theorem pathStabilizer_le_endpoint_ballKernel_of_vertices {n : ℕ} {a b : Vertex F}
    (p : BasedWalk (graph F) n a) (q : BasedWalk (graph F) n b)
    (g : G) (he : p.vertices.map (g • ·) = q.vertices) (k : ℕ)
    (hle : pathStabilizer F p ≤ ballKernel F p.endpoint k) :
    pathStabilizer F q ≤ ballKernel F q.endpoint k := by
  have hact : GraphAction (graph F) G :=
    ⟨fun g _ _ h => (translationGraphIso F g).toHom.map_adj h⟩
  exact pathStabilizer_le_ballKernel_of_vertices F p q g he
    (endpoint_smul_of_vertices hact g p q he) k hle
end Subgroup.CosetGeometry.RankTwo
