module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.Setup
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.MaximalImages
public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.PreparationSource.Normalization

/-!
# Thompson normalization of components in the faithful quotient

A normal elementary two-subgroup lies in every Sylow two-subgroup. The
nontrivial image of each maximum elementary subgroup of that Sylow is a
best offender on the faithful quotient representation. The proved B.1.5(4)
normalization theorem applies to each such image; taking their join proves
C.1.16(1) in the exact quotient presentation consumed by the Y_z selection.
Source: Aschbacher--Smith, B.1.5(4), B.2.5 and C.1.16(1), pp.69,76,125--126.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
universe u

/-- The complete earlier-source normalization input, with all premises discharged. -/
theorem sourceC116One : SourceC116One.{u} := by
  intro H D _ _ _ _ V hV hE _hF q hq hker _hcore S E hEcomponent
  let := hV
  let := hE
  let ρ := NormalElementaryQuotient.representation V q hq hker
  have hf : Function.Injective ρ :=
    NormalElementaryQuotient.representation_injective V q hq hker
  have hVS := (IsElementaryAbelian.isPGroup 2 V).le_sylow_of_normal S
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro A hA
  apply map_le_iff_le_comap.mp
  by_cases hb : A.map q = ⊥
  · rw [hb]
    exact bot_le
  · exact ChapterB.PreparationSource.componentNormalization D (Additive V) ρ hf (A.map q)
      (Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
        V q hq hker (S : Subgroup H) A hVS hA hb) E hEcomponent

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
