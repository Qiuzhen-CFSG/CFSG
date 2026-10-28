module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E7
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.ExceptionalSections

/-!
# The actual characteristic-two E7 section in the A.2 exclusion

The checked root words give a binary symplectic section in a proper
involution centralizer of the literal E7 central quotient. The original
proper-section induction hypothesis applies after lifting this normalizer
through G → G/Z(G).

Source: Aschbacher–Smith A.2.15(2), A.2.18, printed pp.37–40; GLS3 §2.6.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie.ExceptionalSections
universe u v
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- Split E7 over every finite characteristic-two field is excluded using
its actual binary symplectic section and the original proper-section IH. -/
theorem false_of_e7
    (ih : TheoremAOnProperSections K G) (hG : IsQuasithin G) (hK : IsKGroup K G)
    {F : Type v} [Field F] [Finite F] [CharP F 2]
    (e : (G ⧸ Subgroup.center G) ≃* ExceptionalSplit.E7 F) : False :=
  false_of_binary_symplectic_section ih hG hK e
    (Theory.SpecificGroups.LieType.SourceLevi.E7.normalizerSection F)

end CFSG.Quasithin.ChapterA.Section02.EvenLie.ExceptionalSections
