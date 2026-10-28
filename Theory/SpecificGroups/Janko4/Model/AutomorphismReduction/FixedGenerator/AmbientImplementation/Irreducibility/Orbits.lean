module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.AmbientImplementation.Irreducibility.Data
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.AmbientImplementation.Irreducibility.PackedSpan

/-!
# Orbit trees and the left-kernel vector

Each noninitial orbit vector is checked to be the image of an earlier one.
The column orbit uses transposed packed generators; the dual orbit uses the
original rows. See `source/generate.py` and `Model/Data.lean` for provenance.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.IrreducibilityCertificate
open GeneratorCertificates Matrix

set_option maxRecDepth 10000 in
theorem left_annihilates : vecMul (vector leftSeed) (decodeRows testRows) = 0 := by
  rw [← vector_packedRow]
  have h : packedRow leftSeed testRows = 0 := by decide +kernel
  rw [h]
  ext i
  simp [vector, bit]

set_option maxRecDepth 10000 in
theorem column_steps : OrbitSteps columnOrbit columnParents transposeA transposeB := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem row_steps : OrbitSteps rowOrbit rowParents aRows bRows := by
  decide +kernel

theorem column_seed : columnOrbit.get 0 = rightSeed := by decide +kernel
theorem row_seed : rowOrbit.get 0 = leftSeed := by decide +kernel

end Janko4.OuterReduction.FixedGenerator.IrreducibilityCertificate
