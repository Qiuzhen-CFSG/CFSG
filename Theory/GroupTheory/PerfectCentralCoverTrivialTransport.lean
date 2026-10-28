module

public import Theory.GroupTheory.PerfectCentralCoverEmbeddingRigidity

/-!
# Transporting trivial universal kernels through group models

Compose a perfect central cover with a specified model isomorphism. Its
kernel is unchanged, so triviality of the model's canonical universal kernel
makes the original projection injective. Applying this to the canonical
projection transports multiplier triviality across universes without choosing
an isomorphism between universal covering groups.

Source: the perfect central-cover convention of Aschbacher–Smith I.1.1,
printed p.407. The family-specific kernel calculation is a separate input.
-/

public section

namespace PerfectCentralCovering

universe u v w

/-- A model's trivial universal kernel makes the original cover injective,
with its literal projection and no same-universe restriction. -/
theorem Cover.injective_of_model_kernel
    {E : Type u} {G : Type v} {H : Type w} [Group E] [Group G] [Group H]
    (f : Cover E G) (e : G ≃* H) (hk : (universalProjection H).ker = ⊥) :
    Function.Injective f.toMonoidHom := by
  let g : Cover E H :=
    { toMonoidHom := e.toMonoidHom.comp f.toMonoidHom
      surjective := e.surjective.comp f.surjective
      isPerfect := f.isPerfect
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
        exact f.ker_le_center }
  have hi := g.injective_of_universalProjection_ker_eq_bot hk
  intro x y hxy
  apply hi
  exact congrArg e hxy

/-- Triviality of the canonical universal kernel transports along the actual
base isomorphism. Perfectness is required only on the original group. -/
theorem universalProjection_ker_eq_bot_of_mulEquiv
    {G : Type u} {H : Type v} [Group G] [Group H] [Group.IsPerfect G]
    (e : G ≃* H) (hk : (universalProjection H).ker = ⊥) :
    (universalProjection G).ker = ⊥ :=
  (universalProjection G).ker_eq_bot_iff.mpr
    ((universalCover G).injective_of_model_kernel e hk)

end PerfectCentralCovering
