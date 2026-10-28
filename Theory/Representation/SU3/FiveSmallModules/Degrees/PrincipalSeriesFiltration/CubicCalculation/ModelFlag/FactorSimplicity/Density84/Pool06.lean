module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.Density84.Pool05

/-!
# Rank reduction stage 7 of the middle-factor witness

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

theorem p54_mem : matrix 84 p54 ∈ Q := by
  exact mul_mem_checked Q p02 p02 p54
    (p02_mem Q hG) (p02_mem Q hG) (by decide +kernel)

theorem p55_mem : matrix 84 p55 ∈ Q := by
  exact mul_mem_checked Q p54 p01 p55
    (p54_mem Q hG) (p01_mem Q hG) (by decide +kernel)

theorem p59_mem : matrix 84 p59 ∈ Q := by
  exact mul_mem_checked Q p12 p01 p59
    (p12_mem Q hG) (p01_mem Q hG) (by decide +kernel)

theorem p60_mem : matrix 84 p60 ∈ Q := by
  exact mul_mem_checked Q p59 p01 p60
    (p59_mem Q hG) (p01_mem Q hG) (by decide +kernel)

theorem p61_mem : matrix 84 p61 ∈ Q := by
  exact mul_mem_checked Q p60 p01 p61
    (p60_mem Q hG) (p01_mem Q hG) (by decide +kernel)

theorem p62_mem : matrix 84 p62 ∈ Q := by
  exact mul_mem_checked Q p61 p02 p62
    (p61_mem Q hG) (p02_mem Q hG) (by decide +kernel)

theorem p63_mem : matrix 84 p63 ∈ Q := by
  exact mul_mem_checked Q p62 p02 p63
    (p62_mem Q hG) (p02_mem Q hG) (by decide +kernel)

theorem p64_mem : matrix 84 p64 ∈ Q := by
  exact scale_mem_checked Q true true p63 p64
    (p63_mem Q hG) (by decide +kernel)

theorem p65_mem : matrix 84 p65 ∈ Q := by
  exact add_mem_checked Q p55 p64 p65
    (p55_mem Q hG) (p64_mem Q hG) (by decide +kernel)

theorem p66_mem : matrix 84 p66 ∈ Q := by
  exact mul_mem_checked Q p52 p65 p66
    (p52_mem Q hG) (p65_mem Q hG) (by decide +kernel)

theorem p67_mem : matrix 84 p67 ∈ Q := by
  exact mul_mem_checked Q p66 p52 p67
    (p66_mem Q hG) (p52_mem Q hG) (by decide +kernel)


end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates.Density84
