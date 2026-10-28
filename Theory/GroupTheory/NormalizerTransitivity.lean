module
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Transporting transitivity of subgroup normalizers

An ambient group isomorphism carrying one subgroup onto another transports
normalizer transitivity on their nonidentity elements.  Map the two elements
forward, use the target normalizer, and pull its conjugator back.

This is the transport used for the four native elementary order-64 Rudvalis
rows in the local inspection of Aschbacher--Smith 4.4.3, pp.622--623.
-/

public section
open Subgroup
namespace Subgroup

/-- Pull back normalizer transitivity along an ambient group isomorphism. -/
theorem normalizer_transitive_of_equiv
    {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (W : Subgroup G) (U : Subgroup H)
    (hWU : W.map e.toMonoidHom = U)
    (htrans : ∀ x y : U, x ≠ 1 → y ≠ 1 →
      ∃ p : normalizer (U : Set H), p.val * x.val * p.val⁻¹ = y.val) :
    ∀ x y : W, x ≠ 1 → y ≠ 1 →
      ∃ p : normalizer (W : Set G), p.val * x.val * p.val⁻¹ = y.val := by
  intro x y hx hy
  let ex : U := ⟨e x, hWU ▸ mem_map_of_mem e.toMonoidHom x.property⟩
  let ey : U := ⟨e y, hWU ▸ mem_map_of_mem e.toMonoidHom y.property⟩
  have hex : ex ≠ 1 := by
    intro h
    apply hx
    apply Subtype.ext
    apply e.injective
    exact (congrArg Subtype.val h).trans (e.map_one.symm)
  have hey : ey ≠ 1 := by
    intro h
    apply hy
    apply Subtype.ext
    apply e.injective
    exact (congrArg Subtype.val h).trans (e.map_one.symm)
  obtain ⟨p,hp⟩ := htrans ex ey hex hey
  have hback : U.map e.symm.toMonoidHom = W := by
    rw [←hWU, map_map]
    have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext z
      exact e.symm_apply_apply z
    rw [he, map_id]
  have hn : e.symm p ∈ normalizer (W : Set G) := by
    rw [←hback]
    exact le_normalizer_map e.symm.toMonoidHom
      (mem_map_of_mem e.symm.toMonoidHom p.property)
  refine ⟨⟨e.symm p, hn⟩, ?_⟩
  apply e.injective
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using hp

end Subgroup
