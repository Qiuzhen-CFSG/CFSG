module

public import Theory.GroupAction.RankTwoCosetCover.RootPathTransitivity

/-!
# Recognizing all automorphisms from a rigid path

In a rank-two coset graph, a type-preserving automorphism first moves its base
vertex by a group translation. Rooted path transitivity then aligns a chosen
nonbacktracking path. An independently established trivial graph fixer forces
the remaining automorphism to be the identity. This isolates the exact extra
rigidity needed beyond transitivity in the binary Ree building application.
-/

public section
namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- Rooted path transitivity plus an independently proved trivial graph fixer
identifies every type-preserving graph automorphism with a group translation. -/
theorem automorphism_eq_translation_of_path_rigid {n : ℕ} {v : Vertex F}
    (p : BasedWalk (graph F) n v) (hp : p.Nonbacktracking)
    (ht : RootPathTransitive (graph F) G v n)
    (hrigid : ∀ a : graph F ≃g graph F,
      (∀ w ∈ p.vertices, a w=w) → a=SimpleGraph.Iso.refl)
    (a : graph F ≃g graph F) (htype : v.type=(a v).type) :
    ∃ g : G, ∀ w, a w=g • w := by
  obtain ⟨g0,hg0⟩ := (same_orbit_iff F v (a v)).mpr htype
  let b : graph F ≃g graph F := a.trans (translationGraphIso F g0⁻¹)
  have hb : b v=v := by
    change g0⁻¹ • a v=v
    rw [←hg0,inv_smul_smul]
  let q : BasedWalk (graph F) n v := BasedWalk.rebase hb (p.map b.toHom)
  have hq : q.Nonbacktracking := by
    apply (BasedWalk.nonbacktracking_rebase _ _).mpr
    apply (BasedWalk.nonbacktracking_map_iff b.toHom _ p).mpr hp
    intro x y z he
    apply Subtype.ext
    exact b.injective (congrArg Subtype.val he)
  obtain ⟨g1,_hg1,hg1⟩ := ht p q hp hq
  have hqv : q.vertices=p.vertices.map b :=
    (BasedWalk.vertices_rebase hb _).trans (BasedWalk.vertices_map b.toHom p)
  have heach : ∀ w ∈ p.vertices, g1 • w=b w :=
    (List.map_inj_left (l := p.vertices)).mp (hg1.trans hqv)
  let d : graph F ≃g graph F := b.trans (translationGraphIso F g1⁻¹)
  have hd : d=SimpleGraph.Iso.refl := hrigid d (by
    intro w hw
    change g1⁻¹ • b w=w
    rw [←heach w hw,inv_smul_smul])
  refine ⟨g0*g1,fun w=>?_⟩
  have hh := congrArg (fun e : graph F ≃g graph F => e w) hd
  change g1⁻¹ • (g0⁻¹ • a w)=w at hh
  simpa only [smul_inv_smul,mul_smul]
    using congrArg (fun x => g0 • g1 • x) hh
end Subgroup.CosetGeometry.RankTwo
