module
public import Theory.Representation.BinaryEndpointInduction.CoordinateCertificates
public import Theory.Representation.BinaryEndpointInduction.SpectralPolynomials
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Polynomial

/-!
# The five literal companion blocks of the endpoint spectral operator

The selected basis turns the spectral operator into five companion blocks
with dimensions1,4,6,14,20. The two endpoint orientations have exactly the
same block operator. Each displayed polynomial is checked to annihilate
its literal block; irreducibility is supplied by the separate polynomial
certificate.
-/
@[expose] public section
namespace BinaryEndpointInduction
open Matrix Polynomial
open SpectralPolynomials

def blockOffset : Fin 5 → ℕ := ![0,1,5,11,25]

def blockMatrix (i : Fin 5) : Matrix (Fin (degree i)) (Fin (degree i)) (ZMod 2) :=
  fun r c => companion false ⟨blockOffset i+r.val,by fin_cases i <;> simp [blockOffset,SpectralPolynomials.degree] at * <;> omega⟩
    ⟨blockOffset i+c.val,by fin_cases i <;> simp [blockOffset,SpectralPolynomials.degree] at * <;> omega⟩

/-- Both literal coordinate systems have the same spectral block matrix. -/
theorem companion_eq : companion true=companion false := by decide +kernel

/-- Each actual block is annihilated by the corresponding irreducible polynomial. -/
theorem block_annihilated (i : Fin 5) : aeval (blockMatrix i) (polynomial i)=0 := by
  fin_cases i
  · change aeval (blockMatrix 0) (X+1 : (ZMod 2)[X])=0
    simp only [map_add,map_one,aeval_X]
    decide +kernel
  · change aeval (blockMatrix 1) (X^4+X+1 : (ZMod 2)[X])=0
    simp only [map_add,map_pow,map_one,aeval_X]
    decide +kernel
  · change aeval (blockMatrix 2) (X^6+X^4+X^3+X+1 : (ZMod 2)[X])=0
    simp only [map_add,map_pow,map_one,aeval_X]
    decide +kernel
  · change aeval (blockMatrix 3) (X^14+X^7+X^5+X^3+1 : (ZMod 2)[X])=0
    simp only [map_add,map_pow,map_one,aeval_X]
    decide +kernel
  · change aeval (blockMatrix 4) (X^20+X^10+X^9+X^7+X^6+X^5+X^4+X+1 : (ZMod 2)[X])=0
    simp only [map_add,map_pow,map_one,aeval_X]
    decide +kernel
end BinaryEndpointInduction
