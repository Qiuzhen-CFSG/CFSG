module

public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.A6Lift.Action

/-!
# Natural coordinates without changing the original cover

A linear marking of the original natural quotient conjugates its ambient
action into the matrix coordinates used by the A₆ cover. The covering
projection becomes exactly the marking composed with the original map.
Its domain, its ambient action and its kernel are unchanged, so the
central-cover hypothesis transports without an extra assumption.

This is the coordinate adapter for the original W/Z application of
Aschbacher--Smith I.2.3 before 14.6.24, printed pp.413 and 1038.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.A6Lift
open Representation Representation.OneCohomology
variable {J N V : Type*} [Group J]
    [AddCommGroup N] [Module (ZMod 2) N]
    [AddCommGroup V] [Module (ZMod 2) V]

/-- The same original actor in the specified natural coordinates. -/
def coordinateAction (η : Representation (ZMod 2) J N)
    (E : N ≃ₗ[ZMod 2] Natural) : Representation (ZMod 2) J Natural :=
  E.conjRingEquiv.toMonoidHom.comp η

theorem coordinateAction_apply (η : Representation (ZMod 2) J N)
    (E : N ≃ₗ[ZMod 2] Natural) (j : J) (v : Natural) :
    coordinateAction η E j v = E (η j (E.symm v)) := rfl

/-- The literal original projection followed by its natural marking. -/
def coordinateProjection {η : Representation (ZMod 2) J N}
    {τ : Representation (ZMod 2) J V} (q : τ.IntertwiningMap η)
    (E : N ≃ₗ[ZMod 2] Natural) : τ.IntertwiningMap (coordinateAction η E) :=
  (E.toLinearMap.comp q.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro j v
    change E (q (τ j v)) = E (η j (E.symm (E (q v))))
    rw [E.symm_apply_apply]
    exact congrArg E (LinearMap.congr_fun (q.isIntertwining' j) v))

theorem coordinateProjection_apply {η : Representation (ZMod 2) J N}
    {τ : Representation (ZMod 2) J V} (q : τ.IntertwiningMap η)
    (E : N ≃ₗ[ZMod 2] Natural) (v : V) : coordinateProjection q E v = E (q v) := rfl

theorem coordinateProjection_isCover {η : Representation (ZMod 2) J N}
    {τ : Representation (ZMod 2) J V} (q : τ.IntertwiningMap η) (hq : IsCover q)
    (E : N ≃ₗ[ZMod 2] Natural) : IsCover (coordinateProjection q E) := by
  refine ⟨E.surjective.comp hq.1, ?_, hq.2.2⟩
  intro v hv
  apply hq.2.1
  change E (q v) = 0 at hv
  exact E.injective (hv.trans (map_zero E).symm)

/-- Compatibility of the given group and vector markings for the original
normal subgroup, with no replacement of its embedding in J. -/
theorem coordinateAction_marked (L : Subgroup J) (e : L ≃* Core)
    (η : Representation (ZMod 2) J N) (E : N ≃ₗ[ZMod 2] Natural)
    (hE : ∀ l : L, ∀ v, E (η l v) = natural e l (E v)) :
    ∀ l : L, ∀ v, coordinateAction η E l v = natural e l v := by
  intro l v
  rw [coordinateAction_apply, hE, E.apply_symm_apply]

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.A6Lift
