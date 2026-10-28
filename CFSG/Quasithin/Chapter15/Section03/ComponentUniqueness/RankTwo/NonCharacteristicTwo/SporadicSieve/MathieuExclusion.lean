module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.Definitions
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoModel
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ModelAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ShadowBounds
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion.M11
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion.M12
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion.M22
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion.M23
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion.M24
public import CFSG.Quasithin.ClassificationModels.Families

/-!
# Exclusion of all Mathieu carriers from the rank-two sporadic sieve

M₁₁ is excluded by its Sylow-containing two-local orders, after proving the
component action is inner. M₁₂ and M₂₂ are excluded inside the actual component
by their solvable-normal-seed coverage, including outer component actions.
For M₂₃ and M₂₄, automorphism innerness and the native local coverage place
the actual normal seed in a geometric local subgroup whose solvable normal
subgroups have order indivisible by nine, contradicting the full shadow.

`not_mathieu` assembles all five branches with actual catalogue-carrier
equivalences. It retains the entire `ComponentSetup`, including relative
normality, maximality at characteristic two and the S₃ × S₃ Frattini shadow.
Source: Aschbacher--Smith, 1.1.5(3f) and 15.3.41--42, printed pp.502 and 1138.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion

/-- The M₁₁ and M₂₂ branches, with actual catalogue-carrier equivalences. -/
theorem not_m11_or_m22 {G : Type*} [Group G] [Finite G]
    {I L M Y S : Subgroup G} [(L.subgroupOf I).Normal]
    (d : ComponentSetup I L M Y S) (name : ClassificationModels.SporadicName)
    (hn : name = .m11 ∨ name = .m22) (e : L ⧸ pCore 2 L ≃* name.Carrier) : False := by
  rcases hn with rfl | rfl
  · exact not_m11 d e
  · exact not_m22 d e

/-- None of the five actual Mathieu carriers can occur in the source
component setup, including every possible automorphism extension. -/
theorem not_mathieu {G : Type*} [Group G] [Finite G]
    {I L M Y S : Subgroup G} [(L.subgroupOf I).Normal]
    (d : ComponentSetup I L M Y S) (name : ClassificationModels.SporadicName)
    (hn : name = .m11 ∨ name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24)
    (e : L ⧸ pCore 2 L ≃* name.Carrier) : False := by
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact not_m11 d e
  · exact not_m12 d e
  · exact not_m22 d e
  · exact not_m23 d e
  · exact not_m24 d e

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion
