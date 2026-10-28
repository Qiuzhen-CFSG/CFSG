module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.LocalExtension
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.FieldCompatibility
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.FieldAction

/-!
# Field extensions of the actual standard locals

The short and long rank-one local groups carry restrictions of the genuine
coefficientwise octonion field action. Their explicit SL₂ representations,
followed by the central projection to PSL₂, give equivariant surjections
whose kernels are exactly the respective five-root radicals.

Applying the local automorphism-kernel calculation proves that a faithful
finite field-automorphism extension has the same two-core. Moreover, an
element acts inner on the PSL₂ quotient exactly when its field actor is
trivial. This discharges the local-map and kernel inputs for both concrete
G₂ locals, rather than leaving them as new assumptions of the application.
The actor need not be a two-group; the source's two-group case is included.
At F₂ these are still locals in full G₂(2), not in its derived subgroup.

Source: the two-core equality and inner-quotient-action step in
Aschbacher--Smith F.1.12, printed p.264. The concrete representations and
coefficient transport come from the licensed ATLAS model and checked
extensions imported above.
-/

@[expose] public section

namespace Atlas.G2.LieAutomorphismExtensions
open LieParabolicSetup Atlas.RankOneFieldAutomorphisms
open scoped MatrixGroups
variable {F : Type*} [Field F]

/-- The genuine coefficientwise action restricted to the short local group. -/
def shortFieldAction : (F ≃+* F) →* MulAut (local₁ (F := F)) where
  toFun := local₁FieldEquiv
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    rfl

/-- The restricted short action is the actual full-model coefficient action. -/
@[simp] theorem shortFieldAction_apply_val (σ : F ≃+* F) (g : local₁ (F := F)) :
    (shortFieldAction σ g).val = fieldAction σ g.val := rfl

variable [CharP F 2]

/-- The genuine coefficientwise action restricted to the long local group. -/
def longFieldAction : (F ≃+* F) →* MulAut (local₂ (F := F)) where
  toFun := local₂FieldEquiv
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    rfl

/-- The short local representation followed by the actual central quotient. -/
def shortPSLHom : local₁ (F := F) →* PSL(2,F) :=
  (QuotientGroup.mk' (Subgroup.center SL(2,F))).comp shortSLHom

/-- The long local representation followed by the actual central quotient. -/
def longPSLHom : local₂ (F := F) →* PSL(2,F) :=
  (QuotientGroup.mk' (Subgroup.center SL(2,F))).comp longSLHom

theorem shortPSLHom_surjective : Function.Surjective (shortPSLHom (F := F)) :=
  (QuotientGroup.mk'_surjective _).comp shortSLHom_surjective

theorem longPSLHom_surjective : Function.Surjective (longPSLHom (F := F)) :=
  (QuotientGroup.mk'_surjective _).comp longSLHom_surjective

/-- The short quotient kernel is the literal five-root radical inside the local group. -/
theorem shortPSLHom_ker : (shortPSLHom (F := F)).ker = radical₁.subgroupOf local₁ := by
  rw [shortPSLHom, MonoidHom.ker_comp_of_injective _ _ sl_project_injective, shortSLHom_ker]

/-- The long quotient kernel is the literal five-root radical inside the local group. -/
theorem longPSLHom_ker : (longPSLHom (F := F)).ker = radical₂.subgroupOf local₂ := by
  rw [longPSLHom, MonoidHom.ker_comp_of_injective _ _ sl_project_injective, longSLHom_ker]

/-- The short quotient intertwines the actual coefficient actions. -/
theorem shortPSLHom_field (σ : F ≃+* F) (g : local₁ (F := F)) :
    shortPSLHom (shortFieldAction σ g) = fieldEquivPSL 2 σ (shortPSLHom g) := by
  change QuotientGroup.mk' _ (shortSLHom (local₁FieldEquiv σ g)) = _
  rw [shortSLHom_field]
  exact (fieldEquivPSL_mk 2 σ (shortSLHom g)).symm

/-- The long quotient intertwines the actual coefficient actions. -/
theorem longPSLHom_field (σ : F ≃+* F) (g : local₂ (F := F)) :
    longPSLHom (longFieldAction σ g) = fieldEquivPSL 2 σ (longPSLHom g) := by
  change QuotientGroup.mk' _ (longSLHom (local₂FieldEquiv σ g)) = _
  rw [longSLHom_field]
  exact (fieldEquivPSL_mk 2 σ (longSLHom g)).symm

/-- The restricted long action is the actual full-model coefficient action. -/
@[simp] theorem longFieldAction_apply_val (σ : F ≃+* F) (g : local₂ (F := F)) :
    (longFieldAction σ g).val = fieldAction σ g.val := rfl

variable {A : Type*} [Group A] (σ : A →* (F ≃+* F))

/-- The short-local field extension has precisely the original five-root radical as its two-core. -/
theorem shortFieldExtension_twoCore [Finite F] [Finite A]
    (hσ : Function.Injective σ) :
    pCore 2 ((local₁ (F := F)) ⋊[shortFieldAction.comp σ] A) =
      (radical₁.subgroupOf local₁).map
        (SemidirectProduct.inl : local₁ →* (local₁ (F := F)) ⋊[shortFieldAction.comp σ] A) := by
  have hk : IsPGroup 2 (shortPSLHom (F := F)).ker := by
    rw [shortPSLHom_ker, ← local₁_intrinsic_pCore]
    exact pCore_isPGroup
  have h := localExtension_twoCore shortPSLHom (shortFieldAction.comp σ) σ
    (fun a g => shortPSLHom_field (σ a) g) shortPSLHom_surjective hσ hk
  rwa [shortPSLHom_ker] at h

/-- The long-local field extension has precisely the original five-root radical as its two-core. -/
theorem longFieldExtension_twoCore [Finite F] [Finite A]
    (hσ : Function.Injective σ) :
    pCore 2 ((local₂ (F := F)) ⋊[longFieldAction.comp σ] A) =
      (radical₂.subgroupOf local₂).map
        (SemidirectProduct.inl : local₂ →* (local₂ (F := F)) ⋊[longFieldAction.comp σ] A) := by
  have hk : IsPGroup 2 (longPSLHom (F := F)).ker := by
    rw [longPSLHom_ker, ← local₂_pCore]
    exact pCore_isPGroup
  have h := localExtension_twoCore longPSLHom (longFieldAction.comp σ) σ
    (fun a g => longPSLHom_field (σ a) g) longPSLHom_surjective hσ hk
  rwa [longPSLHom_ker] at h

/-- Inner action on the actual short-local PSL₂ quotient forces the field actor to be trivial. -/
theorem shortFieldExtension_inner_iff (hσ : Function.Injective σ)
    (z : (local₁ (F := F)) ⋊[shortFieldAction.comp σ] A) :
    (∃ g : PSL(2,F),
      localQuotientAction shortPSLHom (shortFieldAction.comp σ) σ
        (fun a x => shortPSLHom_field (σ a) x) z = MulAut.conj g) ↔ z.right = 1 :=
  localQuotientAction_inner_iff _ _ _ _ hσ z

/-- Inner action on the actual long-local PSL₂ quotient forces the field actor to be trivial. -/
theorem longFieldExtension_inner_iff (hσ : Function.Injective σ)
    (z : (local₂ (F := F)) ⋊[longFieldAction.comp σ] A) :
    (∃ g : PSL(2,F),
      localQuotientAction longPSLHom (longFieldAction.comp σ) σ
        (fun a x => longPSLHom_field (σ a) x) z = MulAut.conj g) ↔ z.right = 1 :=
  localQuotientAction_inner_iff _ _ _ _ hσ z

end Atlas.G2.LieAutomorphismExtensions
