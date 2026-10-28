module

public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.Cubic
public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.FiveArithmetic

/-!
# Actual source inputs for the Chapter J endgame

The original type-Ru hypotheses supply the Sylow and Singer choices and all
J.2.4–6 and J.2.8 inputs. The opening cubic argument supplies the actual
marked M10 quotient without separate local, Sylow or fusion witnesses.
The five-core arithmetic consumes only the independent geometric inverter
construction. The Aut(A6) normalizer and its subsequent fusion conclusions
remain separate source obligations; this boundary does not assume them.

Source: Aschbacher–Smith, J.1–2, printed pp.431–438.
-/

public section
namespace CFSG.Quasithin.ChapterJ.SourceCompletion
open Subgroup Centralizers
variable {G : Type*} [Group G] [Finite G]

/-- The opening local and cubic package comes directly from IsTypeRu. -/
theorem exists_opening_source (h : IsTypeRu G) :
    ∃ (d : LocalSetup G) (c : Choices d),
      Fusion.SourceJ24 d.toTypeRuSetup ∧
      Fusion.SourceJ25 d.toTypeRuSetup c.sylowThree ∧
      Fusion.SourceJ26 d.toTypeRuSetup c.z ∧
      Fusion.SourceJ28 d.toTypeRuSetup c.z ∧
      Nonempty (c.CubicQuotient ≃* AlternatingSix.M10.extension) ∧
      (∀ i ∈ c.GB, orderOf i = 2 → IsConj i c.z) ∧
      Nat.card c.GB = 2160 ∧ Nat.card c.NormalizerQuotient = 1440 := by
  obtain ⟨d⟩ := h.nonempty_localSetup
  obtain ⟨c⟩ := exists_choices d
  obtain ⟨e, _⟩ := cubic_quotient c
  have hf := fusion c
  exact ⟨d, c, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2,
    ⟨e⟩, cubic_involutions c, GB_card c, normalizer_quotient_card c⟩

end CFSG.Quasithin.ChapterJ.SourceCompletion
