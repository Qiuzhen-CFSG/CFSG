module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.BranchInputs
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.FlagTools
public import ABG.Basic

/-!
# The fixed matrix-field cubic calculation and its exact flag interface

The matrix field is GF(25) with fifth-power conjugation. The representation
coefficient field remains arbitrary of characteristic two. A three-step
invariant flag records the dimensions 21, 84, 21 of its literal quotient
spaces; irreducibility on those same quotient actions is a separate input.
The flag assembly theorem turns these two inputs into the required finite
filtration. This module does not construct the flag or prove its simplicity.

Source motivation: Guralnick–Malle, Proposition 4.3, p.10; Aschbacher–Smith
K.2, p.453. The retained GAP calculation is diagnostic evidence only.
-/

public noncomputable section

open BenderSuzuki.MatrixGroups
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation
universe u v
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The fixed matrix field for the remaining finite calculation. The
coefficient field of the representation is still arbitrary. -/
abbrev MatrixField := GaloisField 5 2

/-- The input form whose standard group has the antidiagonal Gram matrix
and fifth-power conjugation. -/
abbrev modelForm : HermitianForm 3 MatrixField := ABG.unitaryForm 3 5 1 (by decide)

theorem modelForm_conj (x : MatrixField) : modelForm.conj x = x ^ 5 := by
  simp only [modelForm, ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]

/-- The concrete calculation that remains to be proved. In particular it
requires the original coefficient field, not only GF(4). -/
@[expose] def ModelFiltrations : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ),
    χ ≠ 1 → (∀ b, χ b ^ 3 = 1) →
    FactorDegreeFiltration {21, 84}
      (ind (standardBorel modelForm).subtype (scalarCharacter χ))

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation
universe v

/-- An actual invariant three-step flag. The dimensions belong to the literal
successive quotient spaces; simplicity is a separate obligation. -/
structure ThreeStepFlag {K G V : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module K V] (ρ : Representation K G V) where
  stage : ℕ → Subrepresentation ρ
  zero : stage 0 = ⊥
  top : stage 3 = ⊤
  nested : ∀ m, m < 3 → stage m ≤ stage (m + 1)
  degree : ∀ m, m < 3 →
    Module.finrank K ((stage (m + 1)).toSubmodule ⧸
      (within (stage m) (stage (m + 1))).toSubmodule) = if m = 1 then 84 else 21

/-- Irreducibility on the literal successive quotient actions of the flag. -/
@[expose] def ThreeStepFlag.Simple {K G V : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module K V] {ρ : Representation K G V} (s : ThreeStepFlag ρ) : Prop :=
  ∀ m, m < 3 → IsIrreducible (within (s.stage m) (s.stage (m + 1))).quotientRepresentation

/-- Combine the invariant flag and its separate simplicity checks. -/
theorem ThreeStepFlag.filtration {K G V : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module K V] {ρ : Representation K G V}
    (s : ThreeStepFlag ρ) (hs : s.Simple) : FactorDegreeFiltration {21, 84} ρ := by
  apply filtration_of_flag {21, 84} 3 s.stage s.zero s.top s.nested hs
  intro m hm
  rw [s.degree m hm]
  split_ifs <;> simp

/-- The flag construction problem on the fixed matrix field. It retains
every coefficient field and every nontrivial cubic Borel character. -/
@[expose] def ModelFlags :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ),
    χ ≠ 1 → (∀ b, χ b ^ 3 = 1) →
      ThreeStepFlag (ind (standardBorel modelForm).subtype (scalarCharacter χ))

/-- Assemble the concrete filtration from an invariant flag and the checks
on that exact flag's quotient actions. Both inputs remain explicit. -/
theorem model_filtrations_of_simple_flags (s : ModelFlags.{v})
    (hs : ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (χ : standardBorel modelForm →* Kˣ) (hne : χ ≠ 1) (hcube : ∀ b, χ b ^ 3 = 1),
      (s K χ hne hcube).Simple) : ModelFiltrations.{v} := by
  intro K _ _ _ χ hne hcube
  exact (s K χ hne hcube).filtration (hs K χ hne hcube)

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation

