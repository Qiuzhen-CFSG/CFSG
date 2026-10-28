module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.F4
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E6
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.TwistedE6
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.ExceptionalSections
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.ExceptionalSections.Source.E7
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.ExceptionalSections.Source.E8

/-!
# Exceptional exclusions from their actual binary symplectic sections

The literal root-word constructions supply binary Sp6 sections in the
proper normalizers of specified root involutions in F4, E6, E7, E8 and twisted E6.
The existing marked-section
rank bound lifts that normalizer through G → G/Z(G) and uses induction only
on a proper section of G. No quasithinness of the central quotient is assumed.

Source: Aschbacher–Smith A.2.15(2), A.2.18, printed pp.37–40; GLS3 §2.6.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie.ExceptionalSections
universe u v
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- F4 over every finite field of characteristic two is excluded, including
order two, using the original group's smaller-section induction hypothesis. -/
theorem false_of_f4
    (ih : TheoremAOnProperSections K G) (hG : IsQuasithin G) (hK : IsKGroup K G)
    {F : Type v} [Field F] [Finite F] [CharP F 2]
    (e : (G ⧸ Subgroup.center G) ≃* ExceptionalSplit.F4 F) : False :=
  false_of_binary_symplectic_section ih hG hK e
    (Theory.SpecificGroups.LieType.SourceLevi.F4.normalizerSection F)

/-- Split E6 in every finite characteristic-two field is excluded using the
actual binary symplectic section in its proper involution centralizer. -/
theorem false_of_e6
    (ih : TheoremAOnProperSections K G) (hG : IsQuasithin G) (hK : IsKGroup K G)
    {F : Type v} [Field F] [Finite F] [CharP F 2]
    (e : (G ⧸ Subgroup.center G) ≃* ExceptionalSplit.E6 F) : False :=
  false_of_binary_symplectic_section ih hG hK e
    (Theory.SpecificGroups.LieType.SourceLevi.E6.normalizerSection F)

/-- Twisted E6 is excluded at every even parameter, including q=2, using its
literal defining-characteristic subgroup and its own center quotient. -/
theorem false_of_twisted_e6
    (ih : TheoremAOnProperSections K G) (hG : IsQuasithin G) (hK : IsKGroup K G)
    (m : ℕ) (e : (G ⧸ Subgroup.center G) ≃* TwistedE6.Model 2 m) : False :=
  false_of_binary_symplectic_section ih hG hK e
    (Theory.SpecificGroups.LieType.SourceLevi.Twisted.normalizerSection m)

end CFSG.Quasithin.ChapterA.Section02.EvenLie.ExceptionalSections
