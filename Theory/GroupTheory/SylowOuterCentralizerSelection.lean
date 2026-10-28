module
public import Theory.GroupTheory.SylowCentralizerRepresentative
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Saturated outer representatives and normal centralizer intersections

An element outside a normal subgroup stays outside under conjugacy. Choose
its representative in the specified Sylow with Sylow centralizer, then
restrict that centralizer Sylow to the normal subgroup. The latter restriction
keeps the same representative and the literal ambient intersection.

This supplies the saturation premise in Aschbacher--Smith F.4.37, printed
p.293 of refs/quasithin.pdf. It does not promote a local centralizer Sylow
to a Sylow subgroup of a larger ambient group.
-/

public noncomputable section
open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_outer_with_centralizer_sylow (S : Sylow p G)
    (N : Subgroup G) [N.Normal] (x : G) (n : ℕ)
    (hx : orderOf x = p^n) (hxo : x ∉ N) :
    ∃ y : S, orderOf (y : G) = p^n ∧ (y : G) ∉ N ∧
      ∃ Q : Sylow p (centralizer ({(y : G)} : Set G)),
        (Q : Subgroup _).map (centralizer ({(y : G)} : Set G)).subtype =
          (S : Subgroup G) ⊓ centralizer ({(y : G)} : Set G) := by
  obtain ⟨y,hxy,Q,hQ⟩ := S.exists_isConj_with_centralizer_sylow x n hx
  obtain ⟨b,hb⟩ := isConj_iff.mp hxy
  have ho : orderOf (y : G) = p^n := by
    have hh := (MulAut.conj b).orderOf_eq x
    change orderOf (b*x*b⁻¹) = orderOf x at hh
    rw [hb,hx] at hh
    exact hh
  have hyo : (y : G) ∉ N := by
    intro hy
    have hh := (inferInstance : N.Normal).conj_mem (y : G) hy b⁻¹
    rw [←hb] at hh
    have he : b⁻¹ * (b*x*b⁻¹) * (b⁻¹)⁻¹ = x := by group
    exact hxo (he ▸ hh)
  exact ⟨y,ho,hyo,Q,by rw [hQ,subgroupOf_map_subtype]⟩

/-- Restrict a saturated centralizer to a normal subgroup. -/
theorem centralizer_normal_intersection (S : Sylow p G) (N : Subgroup G) [N.Normal]
    (y : G) (Q : Sylow p (centralizer ({y} : Set G)))
    (hQ : (Q : Subgroup _).map (centralizer ({y} : Set G)).subtype =
      (S : Subgroup G) ⊓ centralizer ({y} : Set G)) :
    ∃ R : Sylow p (N ⊓ centralizer ({y} : Set G) : Subgroup G),
      (R : Subgroup _).map (N ⊓ centralizer ({y} : Set G)).subtype =
        (S : Subgroup G) ⊓ (N ⊓ centralizer ({y} : Set G)) := by
  let C := centralizer ({y} : Set G)
  let K := N ⊓ C
  let NN := N.subgroupOf C
  obtain ⟨R,hR⟩ := Q.exists_subgroupOf_eq_of_normal NN
  let e : NN ≃* K :=
    (MulEquiv.subgroupCongr (inf_subgroupOf_right N C).symm).trans
      (subgroupOfEquivOfLe (inf_le_right : K ≤ C))
  let R' := R.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨R',?_⟩
  ext x
  constructor
  · rintro ⟨v,⟨u,hu,rfl⟩,rfl⟩
    have huQ : u ∈ (Q : Subgroup C).subgroupOf NN := hR ▸ hu
    have huS := hQ ▸ mem_map_of_mem C.subtype huQ
    exact ⟨huS.1,u.property,u.val.property⟩
  · rintro ⟨hxS,hxN,hxC⟩
    let u : NN := ⟨⟨x,hxC⟩,hxN⟩
    have huQ : u.val ∈ (Q : Subgroup C) := by
      have hx : x ∈ (Q : Subgroup C).map C.subtype := hQ ▸ ⟨hxS,hxC⟩
      obtain ⟨v,hv,hvx⟩ := hx
      exact (show v=u.val from Subtype.ext hvx) ▸ hv
    refine ⟨e u,⟨u,?_,rfl⟩,rfl⟩
    rw [hR]
    exact huQ
end Sylow
