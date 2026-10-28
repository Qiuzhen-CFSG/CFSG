module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.Preparation
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# Restricting centrally marked triple-Mathieu actions to the binary field

An F₄-linear action whose distinguished central element acts as omega has
exactly the same invariant subspaces after restriction to F₂. Every field
scalar is a binary linear combination of one and omega, so stability under
the central group element supplies the missing scalar stability. Thus a
faithful irreducible marked F₄ action remains faithful and irreducible over F₂.

The remaining simple-point extension contract is stated on the literal
point restriction of the actual matrix triple cover. It concerns dimension
eighteen only and assumes neither a degree catalogue nor absolute
irreducibility. The nonsimple-point branch is handled in `Nonsimple`.

Source context: Guralnick–Malle, Classification of 2F-modules I,
Proposition 5.1, pp.15–16, and Aschbacher–Smith H.12.1, pp.393–394.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsNine
open Representation Uniqueness.PointRestriction

variable {W : Type*} [AddCommGroup W] [Module F W]
  [Module (ZMod 2) W] [IsScalarTower (ZMod 2) F W]
  (τ : Representation F M22TripleCover W)
  (hs : ∀ w, τ scalar w = (QuadraticAlgebra.omega : F) • w)

/-- Central scalar stability identifies the binary and field invariant-subspace lattices. -/
def markedSubrepresentationEquiv :
    Subrepresentation (restrictScalars (k := ZMod 2) τ) ≃o Subrepresentation τ := by
  refine {
    toFun := fun U => {
      toSubmodule := {
        carrier := U
        zero_mem' := U.toSubmodule.zero_mem
        add_mem' := U.toSubmodule.add_mem
        smul_mem' := ?_ }
      apply_mem_toSubmodule := fun g _ hv => U.apply_mem_toSubmodule g hv }
    invFun := fun U => {
      toSubmodule := U.toSubmodule.restrictScalars (ZMod 2)
      apply_mem_toSubmodule := fun g _ hv => U.apply_mem_toSubmodule g hv }
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := fun {_ _} => Iff.rfl }
  · intro r v hv
    have hr : r = algebraMap (ZMod 2) F r.re + r.im • (QuadraticAlgebra.omega : F) :=
      QuadraticAlgebra.mk_eq_add_smul_omega r.re r.im
    rw [hr, add_smul, algebraMap_smul, smul_assoc, ← hs]
    exact U.toSubmodule.add_mem (U.toSubmodule.smul_mem _ hv)
      (U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule scalar hv))
  · intro U
    apply Subrepresentation.toSubmodule_injective
    rfl
  · intro U
    apply Subrepresentation.toSubmodule_injective
    rfl

include hs in
/-- The specified central field preserves irreducibility upon binary restriction. -/
theorem restrictScalars_isIrreducible [τ.IsIrreducible] :
    (restrictScalars (k := ZMod 2) τ).IsIrreducible :=
  (markedSubrepresentationEquiv τ hs).isSimpleOrder_iff.mpr inferInstance

/-- Restriction of the coefficient field retains the actual faithful operators. -/
theorem restrictScalars_faithful (hf : Function.Injective τ) :
    Function.Injective (restrictScalars (k := ZMod 2) τ) := by
  intro g h he
  apply hf
  ext w
  exact LinearMap.congr_fun he w

/-- The outstanding simple-point extension obstruction. Its point action is
transported through the checked point-stabilizer equivalence; this is a
remaining mathematical premise, not a proved exclusion. -/
def SimplePointExtensionExclusion : Prop :=
  ∀ (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M22TripleCover V),
    Representation.SL3FourLocalCatalogue.CentralQuadratic (pointAction ρ) →
    (pointAction ρ).IsIrreducible → Module.finrank (ZMod 2) V = 18 → False

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsNine
