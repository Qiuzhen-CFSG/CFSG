module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointSchreier
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.Reduction
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.Stabilizer

/-!
# Reduction of the natural-point presentation bound

A checked Tietze replay gives an epimorphism from a two-generator presentation
onto the original 25-generator presentation. A 23-coset cover then reduces the
smaller presentation to an explicit 24-generator subgroup presentation.
The remaining finite bound 443520 is an explicit premise here. In particular,
this module does not yet prove the unconditional `presented_bound`.

Source: John Bray, ATLAS M24G1-P1; see `PointBound/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier

/-- Final arithmetic and transfer, with the remaining subgroup bound explicit. -/
theorem presented_bound_of_stabilizer_bound
    (h : Finite PointBound.Stabilizer.Presented ∧
      Nat.card PointBound.Stabilizer.Presented ≤ 443520) :
    Finite Presented ∧ Nat.card Presented ≤ 10200960 :=
  PointBound.presented_bound_of_reduced_bound
    (PointBound.Stabilizer.reduced_bound_of_stabilizer_bound h)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier
