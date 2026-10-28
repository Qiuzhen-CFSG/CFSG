module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.Density84.Data

/-!
# Rank reduction stage 1 of the middle-factor witness

The packed identities below are reduced in Lean’s kernel and interpreted as
closure under algebra operations. Sequential elaboration bounds certificate
memory without changing Lean’s default thread count.

Source: the fixed cubic quotient computation, Guralnick–Malle Proposition 4.3,
p.10; Aschbacher–Smith K.2, p.453. See `source/README.md`.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates.Density84
open Certificate.Packed

variable (Q : Subalgebra CoefficientField (Matrix (Fin 84) (Fin 84) CoefficientField))
  (hG : ∀ a, middleMatrices a ∈ Q)

theorem p00_mem : matrix 84 p00 ∈ Q := by
  rw [p00, matrix_identity]
  exact Q.one_mem

include hG

theorem p01_mem : matrix 84 p01 ∈ Q := hG 0
theorem p02_mem : matrix 84 p02 ∈ Q := hG 1

theorem p03_mem : matrix 84 p03 ∈ Q := by
  exact mul_mem_checked Q p01 p01 p03
    (p01_mem Q hG) (p01_mem Q hG) (by decide +kernel)

theorem p04_mem : matrix 84 p04 ∈ Q := by
  exact mul_mem_checked Q p03 p01 p04
    (p03_mem Q hG) (p01_mem Q hG) (by decide +kernel)

theorem p05_mem : matrix 84 p05 ∈ Q := by
  exact add_mem_checked Q p04 p00 p05
    (p04_mem Q hG) (p00_mem Q) (by decide +kernel)

theorem p06_mem : matrix 84 p06 ∈ Q := by
  exact mul_mem_checked Q p05 p05 p06
    (p05_mem Q hG) (p05_mem Q hG) (by decide +kernel)

theorem p07_mem : matrix 84 p07 ∈ Q := by
  exact mul_mem_checked Q p06 p06 p07
    (p06_mem Q hG) (p06_mem Q hG) (by decide +kernel)

theorem p08_mem : matrix 84 p08 ∈ Q := by
  exact mul_mem_checked Q p07 p06 p08
    (p07_mem Q hG) (p06_mem Q hG) (by decide +kernel)

theorem p09_mem : matrix 84 p09 ∈ Q := by
  exact mul_mem_checked Q p08 p05 p09
    (p08_mem Q hG) (p05_mem Q hG) (by decide +kernel)


end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates.Density84
