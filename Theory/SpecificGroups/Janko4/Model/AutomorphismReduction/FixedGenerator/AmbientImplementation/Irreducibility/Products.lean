module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.AmbientImplementation.Irreducibility.Data
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.AmbientImplementation.Irreducibility.PackedSpan

/-!
# Inverse and elimination products for binary irreducibility

Packed multiplication, proved sound in `GeneratorCertificates/Packed.lean`,
checks the row elimination identity and left inverses for both orbit matrices.
The witnesses are reproduced by `source/generate.py` from the ATLAS data.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.IrreducibilityCertificate
open GeneratorCertificates Matrix

set_option maxRecDepth 10000 in
theorem elimination_product : packedMul eliminationRows testRows = projectionRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem column_inverse : packedMul columnInverse columnOrbit = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem row_inverse : packedMul rowInverse rowOrbit = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)


end Janko4.OuterReduction.FixedGenerator.IrreducibilityCertificate
