module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.FactorNormalizer
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree.NormalizerComponent

/-!
# Excluding the actual SL3 factor rows of B.5.6 in B.6.9

The original natural/doubled factor row gives coordinates on its literal
image in V/C_V(Y). The constructed normalizer action preserves this same
summand and actor. Map its two invariant parabolics to the actual component
automizer, whose genuine minimal-parabolic theorem gives the contradiction.
No natural-action or scalar-descent premise for the automizer is added.

Source: Aschbacher–Smith B.5.6(3a,b) and B.6.9, printed pp.105 and 116.
The component, orbit and simple/even group assertions remain the preceding
B.6.8 structural inputs; this file discharges the module obstruction.
-/

public section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (Y : Subgroup G) [Y.Normal]
  (A : Subgroup Y) (U : Subrepresentation (ρ.comp Y.subtype))

/-- The original doubled-natural quotient row is impossible for a transitive component. -/
theorem source_repeated_three_factor_excluded
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hL : IsComponent G (A.map Y.subtype)) [IsSimpleGroup (A.map Y.subtype)]
    (heven : 2 ∣ Nat.card (A.map Y.subtype))
    (ho : componentOrbit (A.map Y.subtype) (T : Subgroup G) = pResidual 2 G)
    (hU : U.toSubmodule = moved (ρ.comp Y.subtype) A)
    (F : BinaryField) (r : ℕ) (hr : 0 < r)
    (h : IsRepeatedLinearNatural
      (((fixed (ρ.comp Y.subtype)).quotientImage U).toRepresentation.comp A.subtype) F 3 r) :
    False :=
  component_normalizer_not_repeated_natural_three T hP hL heven ho
    (sourceFactorNormalizerSpace ρ Y A U hU).toRepresentation F r hr
    (source_factor_normalizer_repeated_natural ρ Y A U hU F 3 r h)

/-- The original single-natural quotient row is impossible for a transitive component. -/
theorem source_natural_three_factor_excluded
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hL : IsComponent G (A.map Y.subtype)) [IsSimpleGroup (A.map Y.subtype)]
    (heven : 2 ∣ Nat.card (A.map Y.subtype))
    (ho : componentOrbit (A.map Y.subtype) (T : Subgroup G) = pResidual 2 G)
    (hU : U.toSubmodule = moved (ρ.comp Y.subtype) A)
    (F : BinaryField)
    (h : IsLinearNatural
      (((fixed (ρ.comp Y.subtype)).quotientImage U).toRepresentation.comp A.subtype) F 3) :
    False :=
  component_normalizer_not_natural_three T hP hL heven ho
    (sourceFactorNormalizerSpace ρ Y A U hU).toRepresentation F
    (source_factor_normalizer_natural ρ Y A U hU F 3 h)

end CFSG.Quasithin.ChapterB
