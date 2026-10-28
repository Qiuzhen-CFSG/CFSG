module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.FiniteGroup.Checks

/-!
# Actual special-unitary elements for the finite certificate

The checked raw matrices define elements of the literal antidiagonal SU₃ over
the computable field. The primitive field parameter generates all its units.
The raw right-action identities become identities with the project's actual
root and full-torus homomorphisms. This supplies the finite arithmetic part of
`GroupCertificate`; distinctness and full generation are separate obligations.

Source data and motivation: `Coordinates/source/README.md`, Guralnick–Malle
Proposition 4.3, p.10, and Aschbacher–Smith K.2, p.453.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.InvolutionConjugateBounds.Five.Embedding
open HermitianForm.OddPrimeSylow.NormalizedOuter
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FiniteGroup

/-- The GAP primitive parameter, in the explicitly checked field. -/
def parameter : Fieldˣ := Units.mk0 F25.omega (by decide)

theorem field_powers (x : Field) (hx : x ≠ 0) : ∃ n : Fin 24, x = F25.omega ^ n.val := by
  revert x
  decide +kernel

theorem parameter_generates (k : Fieldˣ) : k ∈ Subgroup.zpowers parameter := by
  obtain ⟨n, hn⟩ := field_powers (k : Field) k.ne_zero
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨(n.val : ℤ), ?_⟩
  apply Units.ext
  simpa only [zpow_natCast, Units.val_pow_eq_pow_val, parameter, Units.val_mk0] using hn.symm

/-- The retained matrices as elements of the actual special-unitary group. -/
def generator (a : Fin 2) : standardGroup fieldForm :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (rawGenerator a)
    (by rw [generator_det]; exact one_ne_zero), by
    rw [(FormTransport.standardForm fieldForm).mem_specialSubgroup_iff]
    constructor
    · exact generator_unitary a
    · apply Units.ext
      exact generator_det a⟩

/-- The retained representatives as actual special-unitary elements. -/
def representative (i : Fin 126) : standardGroup fieldForm :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (rawRepresentative i)
    (by rw [representative_det]; exact one_ne_zero), by
    rw [(FormTransport.standardForm fieldForm).mem_specialSubgroup_iff]
    constructor
    · exact representative_unitary i
    · apply Units.ext
      exact representative_det i⟩

@[simp] theorem generator_val (a : Fin 2) : (generator a).val.val = rawGenerator a := rfl

@[simp] theorem representative_val (i : Fin 126) :
    (representative i).val.val = rawRepresentative i := rfl

/-- The root factor of each retained transition, with its defining equation proved. -/
def root (a : Fin 2) (i : Fin 126) :
    hermitianUnipotentCoord (FormTransport.standardForm fieldForm) :=
  ⟨rootValues a i, root_condition a i⟩

theorem root_matrix (a : Fin 2) (i : Fin 126) :
    hermitianUnipotentMatrix (FormTransport.standardForm fieldForm) (root a i) =
      rootMatrix (rootValues a i).1 (rootValues a i).2 := rfl

theorem torus_matrix (n : ℕ) :
    hermitianTorusMatrix (FormTransport.standardForm fieldForm) (parameter ^ n) =
      torusMatrix n := by
  simp only [hermitianTorusMatrix, Units.val_pow_eq_pow_val, parameter, Units.val_mk0,
    FormTransport.standardForm_conj, fieldForm, torusMatrix]

/-- All 252 identities now use the literal Borel root and full torus. -/
theorem transition (a : Fin 2) (i : Fin 126) :
    representative i * generator a =
      ((principalRootIn fieldForm (root a i) *
        principalTorusIn fieldForm (parameter ^ exponent a i) : standardBorel fieldForm) :
          standardGroup fieldForm) * representative (generatorTarget a i) := by
  apply Subtype.ext
  apply Units.ext
  change rawRepresentative i * rawGenerator a =
    (hermitianUnipotentMatrix _ (root a i) *
      hermitianTorusMatrix _ (parameter ^ exponent a i)) *
        rawRepresentative (generatorTarget a i)
  rw [root_matrix, torus_matrix]
  exact raw_transition a i

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FiniteGroup
