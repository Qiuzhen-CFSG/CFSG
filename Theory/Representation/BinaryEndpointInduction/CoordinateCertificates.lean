module
public import Theory.Representation.BinaryEndpointInduction.Coordinates
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix

/-! # Checked changes of basis for the endpoint induction coordinates
All inverse, intertwining and spectral block identities are checked with
packed binary row arithmetic, whose soundness is proved over ZMod2.
-/
public section
namespace BinaryEndpointInduction
open Thompson.BinaryMatrix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem inverse_check : ∀ dual : Bool, ∀ i : Fin 45,
    rowProduct (changeRows dual)[i.val]! (inverseRows dual) 45 = 2^i.val := by
  decide +kernel

private theorem inverse_reverse_check : ∀ dual : Bool, ∀ i : Fin 45,
    rowProduct (inverseRows dual)[i.val]! (changeRows dual) 45 = 2^i.val := by
  decide +kernel

/-- The supplied change of basis has its specified two-sided inverse. -/
theorem change_inverse (dual : Bool) :
    changeMatrix dual * inverseChangeMatrix dual=1 ∧
      inverseChangeMatrix dual * changeMatrix dual=1 :=
  ⟨decode_mul_one 45 _ _ (inverse_check dual),
   decode_mul_one 45 _ _ (inverse_reverse_check dual)⟩

private theorem intertwine_check : ∀ dual : Bool, ∀ k : Fin 2, ∀ i : Fin 45,
    rowProduct (changeRows dual)[i.val]! (generatorRows dual)[k.val]! 45 =
      rowProduct ((adaptedRows dual)[k.val]!)[i.val]! (changeRows dual) 45 := by
  decide +kernel

/-- The literal generator matrices satisfy the specified change of coordinates. -/
theorem generator_intertwine (dual : Bool) (k : Fin 2) :
    changeMatrix dual * generator dual k=adaptedGenerator dual k * changeMatrix dual := by
  ext i j
  change (∑ x : Fin 45, bit (changeRows dual)[i.val]! x.val *
      bit ((generatorRows dual)[k.val]!)[x.val]! j.val)=
    ∑ x : Fin 45, bit ((adaptedRows dual)[k.val]!)[i.val]! x.val * bit (changeRows dual)[x.val]! j.val
  rw [Fin.sum_univ_eq_sum_range (fun x => bit (changeRows dual)[i.val]! x *
    bit ((generatorRows dual)[k.val]!)[x]! j.val),
    Fin.sum_univ_eq_sum_range (fun x => bit ((adaptedRows dual)[k.val]!)[i.val]! x *
    bit (changeRows dual)[x]! j.val),←bit_rowProduct,←bit_rowProduct,intertwine_check]

private theorem spectral_check : ∀ dual : Bool, ∀ i : Fin 45,
    rowProduct (changeRows dual)[i.val]! (spectralRows dual) 45 =
      rowProduct (companionRows dual)[i.val]! (changeRows dual) 45 := by
  decide +kernel

/-- The spectral matrix has the supplied companion-block coordinates. -/
theorem spectral_intertwine (dual : Bool) :
    changeMatrix dual * spectral dual=companion dual * changeMatrix dual := by
  ext i j
  change (∑ x : Fin 45, bit (changeRows dual)[i.val]! x.val * bit (spectralRows dual)[x.val]! j.val)=
    ∑ x : Fin 45, bit (companionRows dual)[i.val]! x.val * bit (changeRows dual)[x.val]! j.val
  rw [Fin.sum_univ_eq_sum_range (fun x => bit (changeRows dual)[i.val]! x * bit (spectralRows dual)[x]! j.val),
    Fin.sum_univ_eq_sum_range (fun x => bit (companionRows dual)[i.val]! x * bit (changeRows dual)[x]! j.val),
    ←bit_rowProduct,←bit_rowProduct,spectral_check]
end BinaryEndpointInduction
