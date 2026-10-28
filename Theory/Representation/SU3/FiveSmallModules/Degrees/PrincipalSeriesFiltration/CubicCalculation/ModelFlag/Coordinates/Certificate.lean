module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Interface
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.CharacterParameters

/-!
# Finite group identities sufficient for the cubic coordinate comparison

`GroupCertificate` concerns only the actual canonical SU₃(5), its actual
upper-root-and-full-torus Borel, and the retained ordering of 126 coordinates.
It asks for distinct right cosets, two generating elements, and root–torus
factorizations of their 252 transitions. A torus exponent must match the fixed
four-element-field coefficient. It assumes neither a representation equivalence
nor a character parametrization, and no certificate is constructed here.

Characters kill the root factors. A generating torus value therefore supplies
the nontrivial cubic scalar in the original coefficient field. Inverting that
value matches Mathlib induction, and transposing the retained row matrices
matches the coordinate vectors. `Coordinates.lean` applies these facts to the
literal quotient. Source motivation: Guralnick–Malle, Proposition 4.3, p.10;
Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public noncomputable section
open scoped Classical
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.OddPrimeSylow.NormalizedOuter
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Destination of a row basis vector in the retained ordering. -/
def generatorTarget (a : Fin 2) (i : Fin 126) : Fin 126 :=
  if a = 0 then generatorTarget0 i else generatorTarget1 i

/-- Four-element-field code of the retained row coefficient. -/
def generatorCode (a : Fin 2) (i : Fin 126) : ℕ :=
  if a = 0 then generatorCode0 i else generatorCode1 i

theorem generatorMatrix_entry {K : Type*} [Field K] [CharP K 2]
    (z : K) (hz : z ^ 2 + z + 1 = 0) (a : Fin 2) (i j : Fin 126) :
    generatorMatrix z hz a i j =
      if i = generatorTarget a j then evaluate z hz (decode (generatorCode a j)) else 0 := by
  by_cases h : a = 0
  · simp only [generatorMatrix, Matrix.transpose_apply, Matrix.map_apply, rawGenerator,
      generatorTarget, generatorCode, if_pos h]
    split_ifs <;> simp
  · simp only [generatorMatrix, Matrix.transpose_apply, Matrix.map_apply, rawGenerator,
      generatorTarget, generatorCode, if_neg h]
    split_ifs <;> simp

theorem generatorMatrix_single {K : Type*} [Field K] [CharP K 2]
    (z : K) (hz : z ^ 2 + z + 1 = 0) (a : Fin 2) (i : Fin 126) (x : K) :
    (generatorMatrix z hz a).mulVec (Pi.single i x) =
      Pi.single (generatorTarget a i) (evaluate z hz (decode (generatorCode a i)) * x) := by
  ext j
  rw [Matrix.mulVec_single]
  change generatorMatrix z hz a j i * x =
    (Pi.single (generatorTarget a i) (evaluate z hz (decode (generatorCode a i)) * x) : Fin 126 → K) j
  rw [generatorMatrix_entry, Pi.single_apply]
  split_ifs <;> simp

/-- Concrete finite group obligations, independent of coefficient fields and induction. -/
structure GroupCertificate where
  parameter : MatrixFieldˣ
  parameter_generates : ∀ k : MatrixFieldˣ, k ∈ Subgroup.zpowers parameter
  representative : Fin 126 → standardGroup modelForm
  generator : Fin 2 → standardGroup modelForm
  separates : ∀ i j, representative i * (representative j)⁻¹ ∈ standardBorel modelForm → i = j
  generates : Subgroup.closure (Set.range generator) = ⊤
  root : Fin 2 → Fin 126 → hermitianUnipotentCoord (FormTransport.standardForm modelForm)
  exponent : Fin 2 → Fin 126 → ℕ
  transition : ∀ a i, representative i * generator a =
    ((principalRootIn modelForm (root a i) *
      principalTorusIn modelForm (parameter ^ exponent a i) : standardBorel modelForm) :
        standardGroup modelForm) * representative (generatorTarget a i)
  coefficient : ∀ a i, decode (generatorCode a i) =
    (QuadraticAlgebra.omega : CoefficientField) ^ exponent a i

namespace GroupCertificate
variable (d : GroupCertificate)

def factor (a : Fin 2) (i : Fin 126) : standardBorel modelForm :=
  principalRootIn modelForm (d.root a i) *
    principalTorusIn modelForm (d.parameter ^ d.exponent a i)

theorem factor_character {K : Type*} [Field K] (χ : standardBorel modelForm →* Kˣ)
    (a : Fin 2) (i : Fin 126) :
    χ (d.factor a i) = χ (principalTorusIn modelForm d.parameter) ^ d.exponent a i := by
  simp only [factor, map_mul, borel_character_trivial_on_root, map_pow, one_mul]

def scalar {K : Type*} [Field K] (χ : standardBorel modelForm →* Kˣ) : K :=
  (χ (principalTorusIn modelForm d.parameter) : K)⁻¹

theorem scalar_quadratic {K : Type*} [Field K]
    (χ : standardBorel modelForm →* Kˣ) (hne : χ ≠ 1) (hcube : ∀ b, χ b ^ 3 = 1) :
    d.scalar χ ^ 2 + d.scalar χ + 1 = 0 := by
  have hn := character_generator_ne_one modelForm d.parameter d.parameter_generates χ hne
  have hp : (χ (principalTorusIn modelForm d.parameter))⁻¹ ^ 3 = 1 := by
    rw [inv_pow, hcube, inv_one]
  simpa only [scalar, Units.val_inv_eq_inv_val] using
    cubic_scalar_quadratic _ (inv_ne_one.mpr hn) hp

theorem factor_coefficient {K : Type*} [Field K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ) (hz : d.scalar χ ^ 2 + d.scalar χ + 1 = 0)
    (a : Fin 2) (i : Fin 126) :
    (χ (d.factor a i) : K)⁻¹ = evaluate (d.scalar χ) hz (decode (generatorCode a i)) := by
  rw [d.factor_character, d.coefficient, map_pow, evaluate_omega]
  simp only [Units.val_pow_eq_pow_val, inv_pow, scalar]

end GroupCertificate
end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag
