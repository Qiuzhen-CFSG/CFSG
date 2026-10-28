module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Model
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.HeckeAction.Basic

/-!
# The highest-root vector in the binary adjoint model

The rank-one endomorphism E₀₃ has trace zero and has nonzero image in the
literal quotient by the identity line. Direct checks on the four standard
basis vectors give positive-root fixedness, the inactive middle exchange,
and the two active endpoint relations. These relations also descend through
`mkAdjoint`. This fixes the seed and the SL₄ marking used by recognition.

Source: Aschbacher–Smith K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Lemma 4.5 step 2 and Proposition 4.8 step 3A.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Representation
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint

/-- The literal highest-root endomorphism E₀₃, in the trace kernel. -/
def highestRoot : TraceZero :=
  ⟨(LinearMap.proj (3 : Fin 4)).smulRight (Pi.single 0 (1 : ZMod 2)), by
    simp [LinearMap.trace_smulRight]⟩

/-- The highest-root endomorphism is not a scalar. -/
theorem mkAdjoint_highestRoot_ne_zero : mkAdjoint highestRoot ≠ 0 := by
  intro hz
  obtain ⟨c, hc⟩ := (mkAdjoint_eq_zero_iff highestRoot).mp hz
  have he := congrArg (fun f : TraceZero => f.val (Pi.single 3 1) 0) hc
  simp [scalarVector, highestRoot] at he

/-- The trace-zero model has exactly the prescribed local endpoint relations. -/
theorem highestRoot_local : LocalHighestVector traceAction {0, 2} highestRoot := by
  constructor
  · intro i j hij
    apply Subtype.ext
    rw [traceAction_apply]
    apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
    intro k
    ext l
    simp only [LinearMap.comp_apply, Pi.basisFun_apply]
    rw [Matrix.SpecialLinearGroup.transvection_inv]
    revert i j k l hij
    decide
  · intro i hi
    have hi1 : i = 1 := by fin_cases i <;> simp_all
    subst i
    apply Subtype.ext
    rw [traceAction_apply]
    apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
    intro k
    ext l
    simp only [Pi.basisFun_apply]
    revert k l
    decide
  · intro i hi
    apply Subtype.ext
    change highestRoot.val + (traceAction (simpleSwap i) highestRoot).val +
      (traceAction (simpleLower i) highestRoot).val = 0
    rw [traceAction_apply, traceAction_apply,
      inv_eq_of_mul_eq_one_right (HeckeAction.swap_sq i)]
    simp only [simpleLower, Matrix.SpecialLinearGroup.transvection_inv]
    apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
    intro k
    ext l
    simp only [Pi.basisFun_apply]
    revert i k l hi
    decide

/-- The seed is already nonzero before taking the scalar quotient. -/
theorem highestRoot_ne_zero : highestRoot ≠ 0 := by
  intro h
  exact mkAdjoint_highestRoot_ne_zero (by rw [h, map_zero])

/-- The actual adjoint quotient carries the same marked endpoint highest vector. -/
theorem adjoint_highestRoot_local :
    LocalHighestVector adjoint {0, 2} (mkAdjoint highestRoot) := by
  constructor
  · intro i j hij
    rw [adjoint_mk, highestRoot_local.upper_fixed i j hij]
  · intro i hi
    rw [adjoint_mk, highestRoot_local.inactive_fixed i hi]
  · intro i hi
    rw [adjoint_mk, adjoint_mk, ← map_add, ← map_add,
      highestRoot_local.active_relation i hi, map_zero]

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint
