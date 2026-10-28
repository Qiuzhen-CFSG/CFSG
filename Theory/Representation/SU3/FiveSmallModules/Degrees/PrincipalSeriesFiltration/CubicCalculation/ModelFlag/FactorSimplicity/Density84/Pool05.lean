module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.Density84.Pool04

/-!
# Rank reduction stage 6 of the middle-factor witness

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

theorem p50_mem : matrix 84 p50 ∈ Q := by
  exact mul_mem_checked Q p30 p02 p50
    (p30_mem Q hG) (p02_mem Q hG) (by decide +kernel)

theorem p51_mem : matrix 84 p51 ∈ Q := by
  exact mul_mem_checked Q p46 p50 p51
    (p46_mem Q hG) (p50_mem Q hG) (by decide +kernel)

theorem p52_mem : matrix 84 p52 ∈ Q := by
  exact mul_mem_checked Q p51 p46 p52
    (p51_mem Q hG) (p46_mem Q hG) (by decide +kernel)


end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates.Density84
