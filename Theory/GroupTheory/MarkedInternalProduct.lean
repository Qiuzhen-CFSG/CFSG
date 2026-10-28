module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Internal direct products with marked factors

Disjoint commuting subgroups whose join is H give an isomorphism H ≃ A × B.
The multiplication homomorphism is injective by disjointness and has range
the join. Its inverse sends the two given subgroups to the two coordinate
factors, as expressed by the two exact subgroup-map equations below.

This is the elementary internal direct-product construction used in
Aschbacher–Smith, quasithin manuscript, at the completion of Theorem 16.3.7
(printed p.1182 / PDF p.1199).
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G]

/-- An internal direct product, with both coordinate-factor equations. -/
theorem exists_marked_internalProductEquiv
    (H A B : Subgroup G) (hSup : A ⊔ B = H)
    (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set G)) :
    ∃ e : H ≃* A × B,
      (A.subgroupOf H).map e.toMonoidHom = (⊤ : Subgroup A).prod ⊥ ∧
      (B.subgroupOf H).map e.toMonoidHom = (⊥ : Subgroup A).prod ⊤ := by
  have comm : ∀ (a : A) (b : B), Commute (a : G) (b : G) :=
    fun a b => (mem_centralizer_iff.mp (hc a.property) b b.property).symm
  let f := A.subtype.noncommCoprod B.subtype comm
  have hf : Function.Injective f := by
    apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
    simpa using And.intro A.subtype_injective (And.intro B.subtype_injective hd)
  have hr : f.range = H := by
    exact (MonoidHom.noncommCoprod_range A.subtype B.subtype comm).trans
      (by simpa using hSup)
  let e := ((MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)).symm
  refine ⟨e, ?_, ?_⟩
  · rw [map_equiv_eq_comap_symm']
    ext x
    change ((x.1 : G) * x.2 ∈ A) ↔ x ∈ (⊤ : Subgroup A).prod ⊥
    simp only [mem_prod, mem_top, mem_bot, true_and, A.mul_mem_cancel_left x.1.property]
    constructor
    · intro hx
      exact Subtype.ext (disjoint_def.mp hd hx x.2.property)
    · intro hx
      rw [hx]
      exact A.one_mem
  · rw [map_equiv_eq_comap_symm']
    ext x
    change ((x.1 : G) * x.2 ∈ B) ↔ x ∈ (⊥ : Subgroup A).prod ⊤
    simp only [mem_prod, mem_top, mem_bot, and_true, B.mul_mem_cancel_right x.2.property]
    constructor
    · intro hx
      exact Subtype.ext (disjoint_def.mp hd x.1.property hx)
    · intro hx
      rw [hx]
      exact B.one_mem

end Theory.GroupTheory
