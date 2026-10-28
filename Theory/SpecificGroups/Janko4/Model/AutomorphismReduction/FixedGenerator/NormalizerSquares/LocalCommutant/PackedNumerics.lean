module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Arithmetic

/-!
# Finite row certificates for the J₄ local commutant

The cyclic rows, polynomial sum, vanishing seed row and sparse projection
are checked by kernel reduction. Separating these finite checks from their
matrix interpretation lets downstream algebra use their checked equalities.
Source matrices and bit convention: `Janko4/Model/Data.lean`; the untrusted
witnesses are retained in `LocalCommutant/source/commutant-candidate.json`.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
open GeneratorCertificates

set_option maxRecDepth 10000 in
theorem cyclic_rows_packed : ∀ i : Fin 112,
    qRows.get i = (wordRows.get i).get 0 := by decide +kernel

set_option maxRecDepth 10000 in
theorem polynomial_packed : ∀ i : Fin 112,
    xorList (polynomialRows.map (fun v => v.get i)) = rRows.get i := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem projection_packed : ∀ i : Fin 112,
    pRows.get i = 2 ^ i.val ^^^
      ((if i = 0 then 1 else 0) ^^^ (if i = 1 then aRows.get 0 else 0)) := by
  decide +kernel

theorem annihilator_zero_row_packed : rRows.get 0 = 0 := by decide +kernel

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
