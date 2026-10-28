module
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Restricting an equivalence along two embeddings

An equivalence carrying the range of one embedding onto the range of another
restricts to an equivalence of their domains. The conclusion retains the
literal commuting square, so marked subgroup maps can be transported through
it. The affine unitary plane comparisons use this to restrict the same full
comparison to the ordinary plane.
-/

public noncomputable section
namespace MulEquiv
universe u v w z

/-- Restrict an equivalence to two embedded subgroups, retaining the inclusion square. -/
theorem exists_compatible_restriction
    {A : Type u} {B : Type v} {G : Type w} {H : Type z}
    [Group A] [Group B] [Group G] [Group H]
    (i : A →* G) (hi : Function.Injective i)
    (j : B →* H) (hj : Function.Injective j)
    (E : G ≃* H) (h : i.range.map E.toMonoidHom = j.range) :
    ∃ e : A ≃* B, ∀ a, E (i a) = j (e a) := by
  let e := (MonoidHom.ofInjective hi).trans ((E.subgroupMap i.range).trans
    ((MulEquiv.subgroupCongr h).trans (MonoidHom.ofInjective hj).symm))
  refine ⟨e,fun a => ?_⟩
  change E (i a) = j ((MonoidHom.ofInjective hj).symm
    ((MulEquiv.subgroupCongr h) ((E.subgroupMap i.range) (MonoidHom.ofInjective hi a))))
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

end MulEquiv
