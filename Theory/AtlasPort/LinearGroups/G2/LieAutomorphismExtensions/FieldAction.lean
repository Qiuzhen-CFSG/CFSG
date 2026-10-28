module

public import Theory.AtlasPort.LinearGroups.G2.LocalFieldTransport
/-!
# The coefficientwise field action on G₂

The actual split-octonion transport is functorial, hence defines an action
of field automorphisms on the full octonion automorphism group. Its action
on the A-root parameters proves faithfulness. This constructs the field
subgroup; it does not assert that all automorphisms are inner times field.

Source: Aschbacher--Smith, F.1.12, printed pp. 263--264. The coefficient
transport and root formulas come from the licensed ATLAS port imported above.
-/

@[expose] public section

namespace Atlas.G2.LieAutomorphismExtensions
open Atlas.SplitOctonion Explicit
variable {F : Type*} [Field F]

/-- Genuine coefficientwise field automorphisms of the octonion model. -/
def fieldAction : (F ≃+* F) →* MulAut (Model F) where
  toFun := fieldEquiv
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Atlas.Algebra.MultiplicativeLinearAut.ext
    intro x
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro g
    apply Atlas.Algebra.MultiplicativeLinearAut.ext
    intro x
    rfl

/-- The A-root parameters detect the field automorphism. -/
theorem fieldAction_injective : Function.Injective (fieldAction (F := F)) := by
  intro σ τ h
  apply RingEquiv.ext
  intro t
  apply rootA_injective
  have ht := MulEquiv.congr_fun h (rootA t)
  change fieldEquiv σ (rootA t) = fieldEquiv τ (rootA t) at ht
  simpa only [fieldEquiv_rootA] using ht
end Atlas.G2.LieAutomorphismExtensions
