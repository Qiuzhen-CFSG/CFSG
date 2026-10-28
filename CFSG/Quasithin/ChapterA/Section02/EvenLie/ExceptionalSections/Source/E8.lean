module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E8
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.ExceptionalSections

/-!
# The E8 exclusion from its actual symplectic normalizer section

The literal root-word construction supplies a binary Sp6 section in the
proper normalizer of a specified root involution. The marked-section rank
bound lifts that normalizer through the original central quotient map and
uses induction only on a proper section of the original group.

Source: Aschbacher–Smith A.2.15(2), A.2.18, printed pp.37–40; GLS3 §2.6.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie.ExceptionalSections
universe u v
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- Split E8 in every finite field of characteristic two is excluded using
its concrete symplectic section and the original smaller-section induction. -/
theorem false_of_e8
    (ih : TheoremAOnProperSections K G) (hG : IsQuasithin G) (hK : IsKGroup K G)
    {F : Type v} [Field F] [Finite F] [CharP F 2]
    (e : (G ⧸ Subgroup.center G) ≃* ExceptionalSplit.E8 F) : False :=
  false_of_binary_symplectic_section ih hG hK e
    (Theory.SpecificGroups.LieType.SourceLevi.E8.normalizerSection F)

end CFSG.Quasithin.ChapterA.Section02.EvenLie.ExceptionalSections
