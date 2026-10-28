module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.Density84.Pool01

/-!
# Rank reduction stage 3 of the middle-factor witness

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

theorem p29_mem : matrix 84 p29 ∈ Q := by
  exact mul_mem_checked Q p02 p01 p29
    (p02_mem Q hG) (p01_mem Q hG) (by decide +kernel)

theorem p30_mem : matrix 84 p30 ∈ Q := by
  exact mul_mem_checked Q p29 p02 p30
    (p29_mem Q hG) (p02_mem Q hG) (by decide +kernel)

theorem p31_mem : matrix 84 p31 ∈ Q := by
  exact mul_mem_checked Q p30 p01 p31
    (p30_mem Q hG) (p01_mem Q hG) (by decide +kernel)

theorem p32_mem : matrix 84 p32 ∈ Q := by
  exact mul_mem_checked Q p31 p01 p32
    (p31_mem Q hG) (p01_mem Q hG) (by decide +kernel)

theorem p33_mem : matrix 84 p33 ∈ Q := by
  exact mul_mem_checked Q p27 p32 p33
    (p27_mem Q hG) (p32_mem Q hG) (by decide +kernel)

theorem p34_mem : matrix 84 p34 ∈ Q := by
  exact mul_mem_checked Q p33 p27 p34
    (p33_mem Q hG) (p27_mem Q hG) (by decide +kernel)


end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates.Density84
