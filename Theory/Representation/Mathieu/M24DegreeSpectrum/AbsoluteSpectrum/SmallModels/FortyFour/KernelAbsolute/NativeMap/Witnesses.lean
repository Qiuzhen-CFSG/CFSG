module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute.NativeMap.WitnessTables
public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.Packed
/-!
# Packed certificates for the native comparison

The generic XOR decoder proves the field-valued equations from checked integer
identities. Each saved column has zero coordinatewise contraction already in
the even core. The two exterior-action certificates identify its image with
the literal column of `Data.matrix`; all 88 columns are checked.

Source context: James (1973), pp.57–111; GM02 Proposition 5.1, manuscript p.17.
The original witnesses remain in `KernelAbsolute/source/`.
-/

@[expose] public section
open scoped BigOperators
open Sporadic.Mathieu MathieuCode Representation
open Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute.NativeMap.Witnesses
open CoordinateExterior
def packedCombine (cs : P → ℕ) (s : P → Bool) : ℕ :=
  MatrixChecks.combine (fun a : I => MatrixChecks.combine (fun b : I => cs (a,b))
    (fun b => s (a,b))) (fun _ => true)

theorem bit_packedCombine (cs : P → ℕ) (s : P → Bool) (q : ℕ) :
    Data.bit (packedCombine cs s) q =
      ∑ p : P, (if s p then (1 : F) else 0) * Data.bit (cs p) q := by
  change Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.bit _ _ = _
  simp only [packedCombine, MatrixChecks.bit_combine, ite_true, mul_one,
    Fintype.sum_prod_type]
  simp only [mul_comm]
  rfl

theorem contraction_packed_cert : ∀ k : Fin 44, packedCombine rowProduct (selected k) = 0 := by
  decide +kernel

theorem contraction_cert (k : Fin 44) : contracted k = 0 := by
  funext q
  have h := congrArg (fun n => Data.bit n q.val) (contraction_packed_cert k)
  rw [bit_packedCombine] at h
  simp only [selected_bit, decode_product] at h
  exact h.trans (by simp [Data.bit])

def matrixSelected (j : Fin 2) (k i : Fin 44) : Bool :=
  ((Data.columns j)[k.val]?.getD 0).testBit i.val

theorem action_packed_cert : ∀ (j : Fin 2) (k : Fin 44),
    packedCombine (packedExterior j) (selected k) =
      MatrixChecks.combine packedKernel (matrixSelected j k) := by decide +kernel

theorem action_cert (j : Fin 2) (k : Fin 44) : coordsAction (codeColumn j) (coeff k) =
    combine coeff (fun i => Data.matrix j i k) := by
  funext q
  have h := congrArg (fun n => Data.bit n (packedIndex q)) (action_packed_cert j k)
  rw [bit_packedCombine] at h
  change _ = Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.bit _ _ at h
  rw [MatrixChecks.bit_combine] at h
  simp only [selected_bit, decode_exterior] at h
  change (∑ p : P, coeff k p * wedgeCoords (codeColumn j p.1) (codeColumn j p.2) q) =
    ∑ i : Fin 44, Data.bit (packedKernel i) (packedIndex q) * Data.matrix j i k at h
  simp only [decode_kernel] at h
  simpa only [coordsAction, combine, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute.NativeMap.Witnesses
