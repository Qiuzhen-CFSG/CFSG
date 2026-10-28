module

public import Theory.Representation.HigherFieldBorelFixedSpaces.Natural
public import Mathlib.FieldTheory.Finite.Trace

/-!
# Comparing the defining-field and binary duals

Compose a defining-field linear functional with the field trace. The trace
pairing is nondegenerate, so the resulting binary linear map is injective;
equal binary dimensions make it an equivalence. It intertwines the
contragredient actions for the same matrices, and hence the same actual
projective component in odd degree.

Source: the natural/dual comparisons needed in Aschbacher–Smith, proof of
13.8.20, printed pp.954–955. This is a comparison of concrete modules, not
a classification of the FF constituent.
-/

@[expose] public noncomputable section

open Representation Representation.HigherFieldBorelFixedSpaces
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- Compose a defining-field functional with the field trace. -/
def traceDualMap (d : ℕ) : Module.Dual F (Fin d → F) →ₗ[ZMod 2]
    Module.Dual (ZMod 2) (Fin d → F) where
  toFun f := (Algebra.trace (ZMod 2) F).comp (f.restrictScalars (ZMod 2))
  map_add' f g := by ext v; simp
  map_smul' c f := by ext v; simp

/-- Nondegeneracy of trace detects every nonzero defining-field functional. -/
theorem traceDualMap_injective (d : ℕ) : Function.Injective (traceDualMap (F := F) d) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro f hf
  apply LinearMap.ext
  intro v
  apply (traceForm_nondegenerate (ZMod 2) F).1 (f v)
  intro c
  have he := LinearMap.congr_fun hf (c • v)
  simpa only [traceDualMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, LinearMap.map_smul, smul_eq_mul, LinearMap.zero_apply,
    Algebra.traceForm_apply, mul_comm] using he

/-- Both duals have the same binary dimension. -/
def traceDualEquiv (d : ℕ) : Module.Dual F (Fin d → F) ≃ₗ[ZMod 2]
    Module.Dual (ZMod 2) (Fin d → F) :=
  LinearEquiv.ofInjectiveOfFinrankEq (traceDualMap d) (traceDualMap_injective d) (by
    rw [← Module.finrank_mul_finrank (ZMod 2) F (Module.Dual F (Fin d → F)),
      Subspace.dual_finrank_eq, Subspace.dual_finrank_eq, Module.finrank_mul_finrank])

/-- Trace commutes with the contragredient action of the same matrices. -/
theorem traceDualEquiv_intertwines (d : ℕ) (g : SL(d,F))
    (f : Module.Dual F (Fin d → F)) :
    traceDualEquiv d (binaryFieldDual d g f) = (binaryNatural d).dual g (traceDualEquiv d f) := by
  ext v
  rfl

/-- The trace comparison retains the original projective component action. -/
theorem traceDualEquiv_projective_intertwines [CharP F 2]
    {n : ℕ} (hn : Odd n) (hF : Nat.card F = 2 ^ n)
    (g : PSL(3,F)) (f : Module.Dual F (Fin 3 → F)) :
    traceDualEquiv 3 (projectiveBinaryFieldDual hn hF g f) =
      (projectiveBinaryNatural hn hF).dual g (traceDualEquiv 3 f) := by
  apply LinearMap.ext
  intro v
  change Algebra.trace (ZMod 2) F
      (f (binaryNatural 3 (((sl3ProjectiveEquiv hn hF).symm g)⁻¹) v)) =
    Algebra.trace (ZMod 2) F
      (f (binaryNatural 3 ((sl3ProjectiveEquiv hn hF).symm g⁻¹) v))
  rw [(sl3ProjectiveEquiv hn hF).symm.map_inv]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo
