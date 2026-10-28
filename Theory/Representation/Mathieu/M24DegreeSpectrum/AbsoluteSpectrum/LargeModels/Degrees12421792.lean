module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Interface
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1242
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1792

/-!
# The two largest binary M₂₄ candidates

The literal ATLAS matrices are shared by two independent obligations: realize
their transposes as the actions of the two native Witt-design permutations, and
certify that the matrices generate their full matrix algebras. Their conjunction
proves absolute irreducibility via scalar extension of density.

This module proves that assembly and fixes its precise row/column convention.
It does not assert that either outstanding certificate exists. In particular,
checking relations in an unverified presentation cannot produce a
`NativeRealization`.

Sources: James, J. Algebra 27 (1973), 57–111; Guralnick–Malle,
Classification of 2F-modules I, Proposition 5.1, manuscript p.17;
ATLAS files `M24G1-f2r1242B0.m1/.m2`, `M24G1-f2r1792B0.m1/.m2`.
The ATLAS provenance and extraction are in `Degrees12421792/source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels

open Degrees12421792 MatrixDensity

/-- The two concrete applications of the density criterion. The action and
density inputs are independent construction obligations, retained explicitly
until their certificate modules are proved. -/
theorem models12421792_of_matrix_certificates
    (r1242 : NativeRealization Data1242.first Data1242.second)
    (r1792 : NativeRealization Data1792.first Data1792.second)
    (h1242 : DensePair Data1242.first Data1242.second)
    (h1792 : DensePair Data1792.first Data1792.second) :
    Nonempty (BinaryModel 1242) ∧ Nonempty (BinaryModel 1792) :=
  ⟨⟨r1242.toBinaryModel h1242⟩, ⟨r1792.toBinaryModel h1792⟩⟩

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
