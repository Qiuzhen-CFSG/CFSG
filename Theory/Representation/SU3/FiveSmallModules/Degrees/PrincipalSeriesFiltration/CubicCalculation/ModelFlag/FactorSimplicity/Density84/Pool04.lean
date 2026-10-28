module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.Density84.Pool03

/-!
# Rank reduction stage 5 of the middle-factor witness

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

theorem p41_mem : matrix 84 p41 ∈ Q := by
  exact mul_mem_checked Q p11 p02 p41
    (p11_mem Q hG) (p02_mem Q hG) (by decide +kernel)

theorem p42_mem : matrix 84 p42 ∈ Q := by
  exact mul_mem_checked Q p41 p01 p42
    (p41_mem Q hG) (p01_mem Q hG) (by decide +kernel)

theorem p43_mem : matrix 84 p43 ∈ Q := by
  exact mul_mem_checked Q p42 p02 p43
    (p42_mem Q hG) (p02_mem Q hG) (by decide +kernel)

theorem p44_mem : matrix 84 p44 ∈ Q := by
  exact mul_mem_checked Q p43 p02 p44
    (p43_mem Q hG) (p02_mem Q hG) (by decide +kernel)

theorem p45_mem : matrix 84 p45 ∈ Q := by
  exact mul_mem_checked Q p38 p44 p45
    (p38_mem Q hG) (p44_mem Q hG) (by decide +kernel)

theorem p46_mem : matrix 84 p46 ∈ Q := by
  exact mul_mem_checked Q p45 p38 p46
    (p45_mem Q hG) (p38_mem Q hG) (by decide +kernel)


end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates.Density84
