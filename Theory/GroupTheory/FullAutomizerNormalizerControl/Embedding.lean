module
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Full local automizers under subgroup inclusion

A full normalizer action on U inside M remains a full action on its literal
image in the ambient group, realized by elements of M. Transport the
specified automorphism through the inclusion equivalence and retain its
normalizer representative, rather than only the abstract action image.

Source application: Aschbacher–Smith, J.2.10, printed p.438 (PDF p.449),
refs/quasithin.pdf.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A full automizer inside a subgroup remains a full action by that subgroup after inclusion. -/
theorem full_action_on_map_subtype (M : Subgroup G) (U : Subgroup M)
    (h : Function.Surjective U.normalizerMonoidHom) :
    ∀ β : MulAut (U.map M.subtype), ∃ n : normalizer (U.map M.subtype : Set G),
      (n : G) ∈ M ∧ (U.map M.subtype).normalizerMonoidHom n = β := by
  let e := U.equivMapOfInjective M.subtype M.subtype_injective
  intro β
  obtain ⟨x, hx⟩ := h ((MulAut.congr e).symm β)
  let n : normalizer (U.map M.subtype : Set G) :=
    ⟨(x.val : G), U.le_normalizer_map M.subtype (mem_map_of_mem M.subtype x.property)⟩
  refine ⟨n, x.val.property, ?_⟩
  have he : MulAut.congr e (U.normalizerMonoidHom x) = β := by
    rw [hx, (MulAut.congr e).apply_symm_apply]
  rw [← he]
  apply MulEquiv.ext
  intro y
  obtain ⟨z, rfl⟩ := e.surjective y
  change _ = e (U.normalizerMonoidHom x (e.symm (e z)))
  rw [e.symm_apply_apply]
  rfl

end Subgroup
