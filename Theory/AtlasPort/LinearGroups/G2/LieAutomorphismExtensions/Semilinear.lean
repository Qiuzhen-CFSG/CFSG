module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.FieldOuter
public import Theory.AtlasPort.LinearGroups.G2.Simplicity
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The faithful inner-field subgroup of Aut(G₂)

Conjugation and coefficientwise field transport combine to give the actual
semidirect-product action. For a finite field of characteristic two and
order greater than two, simplicity makes G₂ centerless, and the trace test
for field automorphisms makes the combined action faithful.

This constructs the inner-field subgroup and proves injectivity. Surjectivity
onto all abstract automorphisms is a separate automorphism theorem, still
required for the extension classification in Aschbacher--Smith F.1.12,
printed pp.263--264.
-/

@[expose] public section

namespace Atlas.G2.LieAutomorphismExtensions
open Theory.GroupTheory
variable {F : Type*} [Field F]

def semilinearAction : Model F ⋊[fieldAction] (F ≃+* F) →* MulAut (Model F) :=
  SemidirectProduct.lift MulAut.conj fieldAction (by
    intro σ
    apply MonoidHom.ext
    intro x
    apply MulEquiv.ext
    intro y
    change fieldAction σ x * y * (fieldAction σ x)⁻¹ =
      fieldAction σ (x * (fieldAction σ).symm y * x⁻¹)
    simp)

@[simp] theorem semilinearAction_apply (z : Model F ⋊[fieldAction] (F ≃+* F)) :
    semilinearAction z = MulAut.conj z.left * fieldAction z.right := rfl

theorem model_center_eq_bot [Finite F] (hq : 2 < Nat.card F) :
    Subgroup.center (Model F) = ⊥ := by
  let := isSimple hq
  rcases (inferInstance : (Subgroup.center (Model F)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hz : rootF (1 : F) ∈ Subgroup.center (Model F) := h ▸ Subgroup.mem_top _
    exact (rootE_rootF_ne (Subgroup.mem_center_iff.mp hz (rootE 1))).elim

theorem semilinearAction_injective [Finite F] [CharP F 2] (hq : 2 < Nat.card F) :
    Function.Injective (semilinearAction (F := F)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply (semilinearAction (F := F)).ker.eq_bot_iff_forall.mpr
  intro z hz
  have hz' : MulAut.conj z.left * fieldAction z.right = 1 := hz
  have hf : fieldAction z.right = MulAut.conj z.left⁻¹ := by
    simpa only [map_inv] using eq_inv_of_mul_eq_one_right hz'
  have hr : z.right = 1 := fieldAction_eq_conj_implies_one _ _ hf
  have hl : z.left = 1 := by
    apply conj_injective_of_center_eq_bot (model_center_eq_bot hq)
    simpa only [hr, map_one, mul_one] using hz'
  exact SemidirectProduct.ext hl hr
end Atlas.G2.LieAutomorphismExtensions
