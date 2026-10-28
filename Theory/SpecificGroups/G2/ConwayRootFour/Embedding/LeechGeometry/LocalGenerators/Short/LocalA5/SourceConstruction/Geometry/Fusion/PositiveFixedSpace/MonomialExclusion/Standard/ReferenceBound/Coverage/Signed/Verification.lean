module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Coverage.Signed.Data

/-!
# Kernel-checked exhaustion of the normalized square-one parameters

The sixteen checks first exhaust all hex parameters. For each surviving row,
they verify the literal base sign and inverse permutation, then exhaust every
parity parameter using integer masks. The parity-mask bridge is checked against
the actual `parityEncoder` and `StandardCoordinates.flat`. The data generator is
untrusted; every certificate here is reduced by the Lean kernel.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284.
Representative timings and regeneration instructions are in `source/README.md`.
-/

open Atlas.Codes
@[expose] public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound.Coverage.Signed

-- Keep the bounded kernel reductions sequential within this module.
set_option Elab.async false

theorem parity_correct : ∀ (r : Fin 32) (i : Fin 24),
    rho (parityEncoder 5 (decodeParity r)) (StandardCoordinates.flat.symm i) =
      maskBit (parityMasks.get r) i := by decide +kernel

/-- The three independent checks for one column entry. -/
def Verified (q : Fin 16) : Prop :=
  Admitted q ∧ ∀ a, Coordinates q a ∧ PackedCheck q a

instance (q) : Decidable (Verified q) := by unfold Verified; infer_instance

private theorem verified00 : Verified 0 := by decide +kernel

private theorem verified01 : Verified 1 := by decide +kernel

private theorem verified02 : Verified 2 := by decide +kernel

private theorem verified03 : Verified 3 := by decide +kernel

private theorem verified04 : Verified 4 := by decide +kernel

private theorem verified05 : Verified 5 := by decide +kernel

private theorem verified06 : Verified 6 := by decide +kernel

private theorem verified07 : Verified 7 := by decide +kernel

private theorem verified08 : Verified 8 := by decide +kernel

private theorem verified09 : Verified 9 := by decide +kernel

private theorem verified10 : Verified 10 := by decide +kernel

private theorem verified11 : Verified 11 := by decide +kernel

private theorem verified12 : Verified 12 := by decide +kernel

private theorem verified13 : Verified 13 := by decide +kernel

private theorem verified14 : Verified 14 := by decide +kernel

private theorem verified15 : Verified 15 := by decide +kernel

/-- All inputs are checked, including rejected hex and parity parameters. -/
theorem verified (q : Fin 16) : Verified q := by
  fin_cases q
  · exact verified00
  · exact verified01
  · exact verified02
  · exact verified03
  · exact verified04
  · exact verified05
  · exact verified06
  · exact verified07
  · exact verified08
  · exact verified09
  · exact verified10
  · exact verified11
  · exact verified12
  · exact verified13
  · exact verified14
  · exact verified15

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound.Coverage.Signed
