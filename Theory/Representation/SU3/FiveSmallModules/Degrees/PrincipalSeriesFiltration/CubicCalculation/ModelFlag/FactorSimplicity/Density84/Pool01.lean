module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.Density84.Pool00

/-!
# Rank reduction stage 2 of the middle-factor witness

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

include hG

theorem p11_mem : matrix 84 p11 ∈ Q := by
  exact mul_mem_checked Q p01 p02 p11
    (p01_mem Q hG) (p02_mem Q hG) (by decide +kernel)

theorem p12_mem : matrix 84 p12 ∈ Q := by
  exact mul_mem_checked Q p11 p01 p12
    (p11_mem Q hG) (p01_mem Q hG) (by decide +kernel)

theorem p13_mem : matrix 84 p13 ∈ Q := by
  exact mul_mem_checked Q p12 p02 p13
    (p12_mem Q hG) (p02_mem Q hG) (by decide +kernel)

theorem p14_mem : matrix 84 p14 ∈ Q := by
  exact mul_mem_checked Q p13 p02 p14
    (p13_mem Q hG) (p02_mem Q hG) (by decide +kernel)

theorem p15_mem : matrix 84 p15 ∈ Q := by
  exact mul_mem_checked Q p14 p01 p15
    (p14_mem Q hG) (p01_mem Q hG) (by decide +kernel)

theorem p16_mem : matrix 84 p16 ∈ Q := by
  exact mul_mem_checked Q p15 p02 p16
    (p15_mem Q hG) (p02_mem Q hG) (by decide +kernel)

theorem p20_mem : matrix 84 p20 ∈ Q := by
  exact mul_mem_checked Q p04 p01 p20
    (p04_mem Q hG) (p01_mem Q hG) (by decide +kernel)

theorem p21_mem : matrix 84 p21 ∈ Q := by
  exact mul_mem_checked Q p20 p02 p21
    (p20_mem Q hG) (p02_mem Q hG) (by decide +kernel)

theorem p22_mem : matrix 84 p22 ∈ Q := by
  exact mul_mem_checked Q p21 p01 p22
    (p21_mem Q hG) (p01_mem Q hG) (by decide +kernel)

theorem p23_mem : matrix 84 p23 ∈ Q := by
  exact mul_mem_checked Q p22 p02 p23
    (p22_mem Q hG) (p02_mem Q hG) (by decide +kernel)

theorem p25_mem : matrix 84 p25 ∈ Q := by
  exact add_mem_checked Q p16 p23 p25
    (p16_mem Q hG) (p23_mem Q hG) (by decide +kernel)

theorem p26_mem : matrix 84 p26 ∈ Q := by
  exact mul_mem_checked Q p09 p25 p26
    (p09_mem Q hG) (p25_mem Q hG) (by decide +kernel)

theorem p27_mem : matrix 84 p27 ∈ Q := by
  exact mul_mem_checked Q p26 p09 p27
    (p26_mem Q hG) (p09_mem Q hG) (by decide +kernel)


end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates.Density84
