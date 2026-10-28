module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.Density84.Pool07

/-!
# Rank reduction stage 9 of the middle-factor witness

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

theorem p78_mem : matrix 84 p78 ∈ Q := by
  exact mul_mem_checked Q p03 p02 p78
    (p03_mem Q hG) (p02_mem Q hG) (by decide +kernel)

theorem p79_mem : matrix 84 p79 ∈ Q := by
  exact mul_mem_checked Q p78 p02 p79
    (p78_mem Q hG) (p02_mem Q hG) (by decide +kernel)

theorem p80_mem : matrix 84 p80 ∈ Q := by
  exact mul_mem_checked Q p79 p01 p80
    (p79_mem Q hG) (p01_mem Q hG) (by decide +kernel)

theorem p81_mem : matrix 84 p81 ∈ Q := by
  exact mul_mem_checked Q p80 p01 p81
    (p80_mem Q hG) (p01_mem Q hG) (by decide +kernel)

theorem p82_mem : matrix 84 p82 ∈ Q := by
  exact scale_mem_checked Q true true p81 p82
    (p81_mem Q hG) (by decide +kernel)

theorem p83_mem : matrix 84 p83 ∈ Q := by
  exact add_mem_checked Q p11 p82 p83
    (p11_mem Q hG) (p82_mem Q hG) (by decide +kernel)

theorem p84_mem : matrix 84 p84 ∈ Q := by
  exact mul_mem_checked Q p73 p83 p84
    (p73_mem Q hG) (p83_mem Q hG) (by decide +kernel)

theorem p85_mem : matrix 84 p85 ∈ Q := by
  exact mul_mem_checked Q p84 p73 p85
    (p84_mem Q hG) (p73_mem Q hG) (by decide +kernel)


end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates.Density84
