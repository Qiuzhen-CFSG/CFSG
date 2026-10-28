module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Split.Exclusion

/-!
# J.2.7(3) from the original type-Ru hypotheses

The source M₁₀ quotient and involutory inverter give a marked index-two
extension. Restriction to the characteristic A₆ gives two alternatives, and
the source fusion/exponent contradiction excludes the direct product. Thus
the original N_G(B)/B is Aut(A₆), carrying C_G(B)/B to the specified M₁₀.

Source: Aschbacher–Smith J.2.7(3), printed p.436 (PDF p.447).
-/

namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- J.2.7(3) for the literal normalizer quotient, with its M₁₀ marking. -/
public theorem normalizer_equiv_autA6_source :
    ∃ e : c.NormalizerQuotient ≃* AlternatingSix.ShadowLocal.AutA6,
      c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension := by
  rcases c.normalizer_marked_dichotomy_source with h | ⟨e,he⟩
  · exact h
  · exact (c.not_normalizer_split_source e he).elim

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
