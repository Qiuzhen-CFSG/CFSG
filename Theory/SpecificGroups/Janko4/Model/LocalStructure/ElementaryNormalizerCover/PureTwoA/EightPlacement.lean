module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Placement
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.Ordinary

/-!
# The native order-256 normalizer input

The checked native automizer places the whole eight normalizer in a conjugate
of the actual F-normalizer. This discharges the independent native input used
by the exceptional pure-first-class branch; the existing conditional APIs
retain their statements.
Source: Kleidman--Wilson (1988), §2.1, pp.488–489, and Corollary 2.3.6, p.493.
-/
public noncomputable section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA

/-- The exact native-eight premise, proved independently of the pure cover. -/
theorem eightNormalizerPlacement : EightNormalizerPlacement :=
  ⟨ElementaryEightGeometry.nativeFusion * EightAutomizer.Native.c,
    EightAutomizer.Native.nativeEight_one_normalizer_placement⟩

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA
