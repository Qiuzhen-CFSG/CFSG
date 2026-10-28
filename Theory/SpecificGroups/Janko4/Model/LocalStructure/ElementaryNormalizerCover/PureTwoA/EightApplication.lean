module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightPlacement

/-!
# Native eight-centralizer applications with the placement discharged

The independent finite automizer calculation places the whole normalizer of
the native elementary group of order 256 in an actual conjugate F-normalizer.
Here it discharges the exact placement input of the exceptional branch of
Section 2.1, including maximal TWO-local equality and the original arbitrary
radical's full normalizer and core restriction maps. The remaining geometric
hypothesis identifies the full centralizer of the original subgroup with the
native eight under one ambient conjugator.

Source: Kleidman--Wilson (1988), Section 2.1, pp.488--489, and Corollary 2.3.6,
p.493. This does not assert that every pure-first subgroup has this centralizer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA

/-- The native placement theorem supplies the whole-normalizer containment. -/
theorem eight_centralizer_normalizer (X : Subgroup Model) (g : Model)
    (hC : (centralizer (X : Set Model)).map (MulAut.conj g).toMonoidHom =
      ElementaryEightGeometry.nativeEight 1) :
    ∃ k : Model, normalizer (X : Set Model) ≤
      LinearFive.fullNormalizer.map (MulAut.conj (g⁻¹*k)).toMonoidHom :=
  fused_eight_normalizer eightNormalizerPlacement X g hC

/-- At maximal TWO-local level the same literal local is the entire normalizer. -/
theorem eight_centralizer_maximal (X : Subgroup Model) (g : Model)
    (hC : (centralizer (X : Set Model)).map (MulAut.conj g).toMonoidHom =
      ElementaryEightGeometry.nativeEight 1)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ k : Model, normalizer (X : Set Model) =
      LinearFive.fullNormalizer.map (MulAut.conj (g⁻¹*k)).toMonoidHom :=
  fused_eight_maximal eightNormalizerPlacement X g hC hmax

/-- Restriction for an arbitrary original radical, retaining the full local
normalizer, actual conjugator, radicality and both intrinsic core identities. -/
theorem eight_centralizer_radical (P X : Subgroup Model) (hP : P.IsPRadical 2)
    (g : Model)
    (hC : (centralizer (X : Set Model)).map (MulAut.conj g).toMonoidHom =
      ElementaryEightGeometry.nativeEight 1)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ k : Model, let M := LinearFive.fullNormalizer.map (MulAut.conj (g⁻¹*k)).toMonoidHom
      IsTwoLocal M ∧ normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P :=
  fused_eight_radical eightNormalizerPlacement P X hP g hC hNX

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA
