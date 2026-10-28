module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical.TwoCore
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical.Levi
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical.Action

/-!
# The two-core and quotient of the unitary-four plane local

The literal Levi section discharges the surjectivity premise in two-core
recognition. Thus the entire Hermitian unipotent kernel is the actual two-core,
and restriction identifies the quotient with SL₂. Its action on this core is
Hermitian congruence, for every element of the local group.

Source: the radical and quotient calculation for Aschbacher--Smith
F.1.12(I)(6), printed pp.263–264. There is no lower field-size restriction
beyond finite characteristic two. Shortness and residuals are separate results.
-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
open Matrix UnitaryFourFlag UnitaryFourPlaneLocal
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)

/-- The exhaustive Hermitian kernel is the actual two-core. -/
theorem radical_eq_twoCore :
    radical F σ hσ = pCore 2 (localFactor F (form F σ hσ)) :=
  radical_eq_twoCore_of_surjective F σ hσ (factorRestriction_surjective F σ hσ)

/-- Restriction induces the unconditional quotient equivalence. -/
def quotientEquivSL2 :
    (localFactor F (form F σ hσ) ⧸ pCore 2 (localFactor F (form F σ hσ))) ≃*
      SpecialLinearGroup (Fin 2) F :=
  quotientEquivSL2OfSurjective F σ hσ (factorRestriction_surjective F σ hσ)

@[simp] theorem quotientEquivSL2_mk (g : localFactor F (form F σ hσ)) :
    quotientEquivSL2 F σ hσ (QuotientGroup.mk g) =
      factorRestriction F (form F σ hσ) g := rfl

/-- The Hermitian coordinates now parametrize the actual two-core. -/
def twoCoreEquiv : Multiplicative (hermitianMatrices F σ) ≃*
    pCore 2 (localFactor F (form F σ hσ)) :=
  (radicalEquiv F σ hσ).trans (MulEquiv.subgroupCongr (radical_eq_twoCore F σ hσ))

@[simp] theorem twoCoreEquiv_val (X : Multiplicative (hermitianMatrices F σ)) :
    (twoCoreEquiv F σ hσ X).val = (radicalEquiv F σ hσ X).val := rfl

/-- Literal local conjugation agrees with the action of its actual quotient coset. -/
theorem twoCoreEquiv_conj (g : localFactor F (form F σ hσ))
    (X : Multiplicative (hermitianMatrices F σ)) :
    MulAut.conjNormal g (twoCoreEquiv F σ hσ X) =
      twoCoreEquiv F σ hσ (Multiplicative.ofAdd
        (hermitianCongruence F σ hσ
          (quotientEquivSL2 F σ hσ (QuotientGroup.mk g)) X.toAdd)) := by
  apply Subtype.ext
  exact congrArg (fun u : radical F σ hσ => u.val) (radicalEquiv_conj F σ hσ g X)

instance twoCore_elementaryAbelian :
    IsElementaryAbelian 2 (pCore 2 (localFactor F (form F σ hσ))) := by
  rw [← radical_eq_twoCore F σ hσ]
  infer_instance

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
