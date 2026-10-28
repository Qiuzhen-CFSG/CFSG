module

public import Theory.Representation.EndFieldTrace
public import Mathlib.RepresentationTheory.Character
public import Theory.FieldTheory.SpanningFrobeniusPeriod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Binary representations over their Schur field and its algebraic closure

A finite-dimensional irreducible binary representation becomes absolutely
irreducible over its actual endomorphism field. Extending that field to its
algebraic closure preserves irreducibility and faithfulness. The original
binary dimension is the Schur-field degree times the absolute dimension.
The character is fixed by the `r`-th Frobenius precisely when that degree
divides `r`, because the original Schur-field traces span the field.

These statements give the descent step in GLS3, Remark 2.8.8. No finiteness,
simplicity, or classification of the acting group is required. The concrete
Ree tensor classification and the Tits absolute minimum are separate inputs.
-/

@[expose] public section

open scoped MonoidAlgebra TensorProduct
namespace Representation.FrobeniusTensor
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]

/-- The actual commuting endomorphism field of the binary irreducible. -/
abbrev SchurField := Module.End (ZMod 2)[G] ρ.asModule
/-- The algebraic closure of the actual Schur field. -/
abbrev Closure := AlgebraicClosure (SchurField ρ)
/-- Scalar extension of the module over its Schur field. -/
abbrev AbsoluteSpace := Closure ρ ⊗[SchurField ρ] ρ.asModule

noncomputable instance schurFieldCharTwo : CharP (SchurField ρ) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField ρ)).injective 2
noncomputable instance closureCharTwo : CharP (Closure ρ) 2 :=
  charP_of_injective_algebraMap (algebraMap (SchurField ρ) (Closure ρ)).injective 2
noncomputable instance schurModuleFinite : FiniteDimensional (SchurField ρ) ρ.asModule := by
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) ρ.asModule)
  exact Module.Finite.of_finite

/-- The absolutely irreducible scalar extension of the Schur-field action. -/
noncomputable def absoluteRep : Representation (Closure ρ) G (AbsoluteSpace ρ) :=
  Representation.extendScalars (Closure ρ) ρ.endFieldRep

instance absoluteRepIrreducible : (absoluteRep ρ).IsIrreducible := by
  let : IsAbsolutelyIrreducible ρ.endFieldRep := endFieldRep_isAbsolutelyIrreducible ρ
  exact IsAbsolutelyIrreducible.irreducible_of_extension ρ.endFieldRep (Closure ρ)

/-- Passing through the Schur field and its algebraic closure preserves faithfulness. -/
theorem absoluteRep_injective (hρ : Function.Injective ρ) : Function.Injective (absoluteRep ρ) := by
  apply (extendScalars_faithful_iff (Closure ρ) ρ.endFieldRep).mp
  intro g h heq
  apply hρ
  ext v
  have hh := congrArg (fun f : Module.End (SchurField ρ) ρ.asModule =>
    ρ.asModuleEquiv (f (ρ.asModuleEquiv.symm v))) heq
  simpa only [endFieldRep_apply, LinearEquiv.apply_symm_apply] using hh

/-- The dimension tower for the actual scalar-extended action. -/
theorem binary_finrank_eq : Module.finrank (ZMod 2) V =
    Module.finrank (ZMod 2) (SchurField ρ) *
      Module.finrank (Closure ρ) (AbsoluteSpace ρ) := by
  rw [Module.finrank_baseChange, Module.finrank_mul_finrank]
  exact ρ.asModuleEquiv.finrank_eq.symm

/-- The exact Frobenius period of the absolute character is the Schur degree. -/
theorem character_pow_iff (r : ℕ) :
    (∀ g, (absoluteRep ρ).character g ^ (2 ^ r) = (absoluteRep ρ).character g) ↔
      Module.finrank (ZMod 2) (SchurField ρ) ∣ r := by
  rw [← FiniteField.forall_pow_eq_self_iff_finrank_dvd_of_span 2 _
    (span_range_endFieldRep_trace ρ) r]
  apply forall_congr'
  intro g
  have htr : (absoluteRep ρ).character g = algebraMap (SchurField ρ) (Closure ρ)
      (LinearMap.trace (SchurField ρ) ρ.asModule (ρ.endFieldRep g)) :=
    LinearMap.trace_baseChange (ρ.endFieldRep g) (Closure ρ)
  rw [htr, ← map_pow]
  exact (algebraMap (SchurField ρ) (Closure ρ)).injective.eq_iff

/-- The Schur field has positive degree over the binary field. -/
theorem schurField_finrank_pos : 0 < Module.finrank (ZMod 2) (SchurField ρ) := by
  let : Module.Finite (ZMod 2) (SchurField ρ) := Module.Finite.of_finite
  exact Module.finrank_pos

/-- An absolute degree bound passes to the original binary module. -/
theorem absolute_finrank_le_binary :
    Module.finrank (Closure ρ) (AbsoluteSpace ρ) ≤ Module.finrank (ZMod 2) V := by
  rw [binary_finrank_eq ρ]
  exact Nat.le_mul_of_pos_left _ (schurField_finrank_pos ρ)

omit [ρ.IsIrreducible] in
/-- Faithfulness of a finite-dimensional binary action supplies finiteness of
the acting group, without any independent order or presentation calculation. -/
theorem finite_of_faithful_binary (hρ : Function.Injective ρ) : Finite G := by
  let : Finite V := Module.finite_iff_finite.mp (inferInstance : Module.Finite (ZMod 2) V)
  let : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  exact Finite.of_injective ρ hρ

end Representation.FrobeniusTensor
