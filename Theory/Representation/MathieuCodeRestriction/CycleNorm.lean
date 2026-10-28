module

public import Theory.Representation.MathieuCodeRestriction.Actions
public import Mathlib.LinearAlgebra.StdBasis

/-!
# A vanishing odd-order norm on the Mathieu quotients

The product of the native standard generators fixes coordinate 1 and cycles
through the other 23 coordinates. Its norm is computed on the coordinate basis.
On the even-weight core this norm is a constant vector, so it vanishes in both
the code and cocode quotients. This proves the global fixed spaces vanish without
using the irreducibility results or parameter tables of Chapter H.

Source: Aschbacher–Smith, H.13.1 (printed p.395), for the two quotients;
the permutations are the certified native M₂₄ generators.
-/

@[expose] public section
open Sporadic.Mathieu
open scoped BigOperators
namespace MathieuCode
noncomputable section

def cycle23 : M24 := ⟨m24GeneratorA * m24GeneratorB,
  M24.mul_mem m24GeneratorA_mem m24GeneratorB_mem⟩

def cycleNorm : Full →ₗ[ZMod 2] Full :=
  ∑ k : Fin 23, fullRepresentation (cycle23 ^ k.val)

def cycleNormFormula : Full →ₗ[ZMod 2] Full where
  toFun v i := if i = 1 then v 1 else ∑ j ∈ (Finset.univ.erase (1 : Fin 24)), v j
  map_add' v w := by ext i; by_cases hi : i = 1 <;> simp [hi, Finset.sum_add_distrib]
  map_smul' c v := by ext i; by_cases hi : i = 1 <;> simp [hi, Finset.mul_sum, mul_sub]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
theorem cycleNorm_eq : cycleNorm = cycleNormFormula := by
  apply (Pi.basisFun (ZMod 2) (Fin 24)).ext
  intro i
  rw [Pi.basisFun_apply]
  revert i
  decide +kernel

theorem cycleNorm_core (v : Core) :
    cycleNorm v = v.val 1 • BinaryPermutation.allOne (Fin 24) := by
  rw [cycleNorm_eq]
  have hv := (BinaryPermutation.mem_core (Fin 24) v.val).mp v.property
  ext i
  simp [cycleNormFormula, BinaryPermutation.allOne, hv]

end
end MathieuCode
