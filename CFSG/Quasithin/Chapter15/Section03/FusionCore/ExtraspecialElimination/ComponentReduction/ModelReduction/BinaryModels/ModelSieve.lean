module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.Catalogue
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.LocalSections
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.CubicControl
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve.Preparation
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve.SectionTransport

/-!
# The binary field sieve and its literal component quotient

The carrier comparisons reduce the Lie alternatives to PSL₃(2), PSL₄(2),
PSL₅(2), A₆, and the derived octonion G₂(2) carrier. The other alternatives
are A₇ and the even hexacode group. The latter retains its equivariant
identification with an actual irreducible section of U_H/Z and its F₄ action.
The component's intrinsic two-core quotient is identified with L* using
relative C-component membership; no equality of L with its T-closure is used.

Preparation proves the B.5.3 hypotheses on J_H* and perfectness from (i).
The terminal theorem below is conditional on the component analysis: that
analysis still must derive quasisimplicity and `ComponentSectionAlternative`
from the complete B.5.6/B.5.1 alternatives. In particular, this module does
not yet prove the source model-selection step of 15.3.49(l).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1143–1144; B.4.2, B.5.1, B.5.3–B.5.6, and K.1.3.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve

variable {G : Type*} [Group G] [Finite G]

/-- Apply the field sieve to an already established component analysis and
transport its conclusions to L/O₂(L). The exceptional source section is retained
in the first conjunct, under the original SectionAction. -/
theorem intrinsic_binary_of_component_analysis
    (H ZS Z A L : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hAH : A ≤ H) (hLJ : L ≤ localSpan A H)
    (hL : (L.subgroupOf (localSpan A H)).IsCComponent)
    (hclassification : ComponentSectionAlternative action.representation (starImage H L))
    (hquasi : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hfield : NoLargerField (L ⧸ pCore 2 L)) :
    BinarySectionAlternative action.representation (starImage H L) ∧
      BinaryComponentModel (L ⧸ pCore 2 L) ∧
      Theory.GroupTheory.IsQuasisimple (L ⧸ pCore 2 L) := by
  let e := componentStarEquiv H L (hLJ.trans (conjugateSpanBy_le_self hAH))
    (localSpan_component_isCComponent A H L hAH hLJ hL)
  have hs := hclassification.sieve (hfield.of_mulEquiv e.symm)
  let _ := hquasi
  exact ⟨hs, hs.componentModel.of_mulEquiv e,
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv e.symm⟩

/-- The terminal sieve when the component classification is stated on its
actual offender-generated actor J_H*. The section transport preserves the
source subspace, quotient coordinates and group equivalence in the hex branch.
The two classification conclusions remain explicit obligations. -/
theorem intrinsic_binary_of_span_analysis
    (H ZS Z A L : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hAH : A ≤ H) (hLJ : L ≤ localSpan A H)
    (hL : (L.subgroupOf (localSpan A H)).IsCComponent)
    (hclassification : ComponentSectionAlternative
      (action.representation.comp (starImage H (localSpan A H)).subtype)
      (starComponent H A L))
    (hquasi : Theory.GroupTheory.IsQuasisimple (starComponent H A L))
    (hfield : NoLargerField (L ⧸ pCore 2 L)) :
    BinarySectionAlternative action.representation (starImage H L) ∧
      BinaryComponentModel (L ⧸ pCore 2 L) ∧
      Theory.GroupTheory.IsQuasisimple (L ⧸ pCore 2 L) := by
  let _ := hquasi
  let e : starComponent H A L ≃* starImage H L :=
    subgroupOfEquivOfLe (map_mono (comap_mono hLJ))
  exact intrinsic_binary_of_component_analysis H ZS Z A L action hAH hLJ hL
    (hclassification.of_subgroupOf (map_mono (comap_mono hLJ)))
    (Theory.GroupTheory.IsQuasisimple.of_mulEquiv e) hfield

/-- The quotient-to-cover equivalence in the exceptional branch, using the
same component comparison as the source section action. -/
noncomputable def intrinsicHexEquiv
    (H ZS Z L : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hLH : L ≤ H) (hL : (L.subgroupOf H).IsCComponent)
    (s : HexSection action.representation (starImage H L)) :
    (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms :=
  (componentStarEquiv H L hLH hL).trans s.groupEquiv

/-- Transporting the component carrier preserves the concrete field-linear
action on the literal source section, not only its binary dimension. -/
theorem intrinsicHexEquiv_equivariant
    (H ZS Z L : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hLH : L ≤ H) (hL : (L.subgroupOf H).IsCComponent)
    (s : HexSection action.representation (starImage H L))
    (g : L ⧸ pCore 2 L)
    (v : centralQuotient action.representation (starImage H L) s.space) :
    s.moduleEquiv
        (centralQuotientRepresentation action.representation (starImage H L) s.space s.stable
          (componentStarEquiv H L hLH hL g) v) =
      Representation.Hexacode.evenFieldAction
        (intrinsicHexEquiv H ZS Z L action hLH hL s g) (s.moduleEquiv v) :=
  s.fieldAction _ _

/-- In the exceptional branch quasisimplicity follows from the proved cover
theorem and the actual component equivalence. -/
theorem intrinsic_quasisimple_of_hexSection
    (H ZS Z L : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hLH : L ≤ H) (hL : (L.subgroupOf H).IsCComponent)
    (s : HexSection action.representation (starImage H L)) :
    Theory.GroupTheory.IsQuasisimple (L ⧸ pCore 2 L) := by
  let _ := s.quasisimple
  exact Theory.GroupTheory.IsQuasisimple.of_mulEquiv
    (componentStarEquiv H L hLH hL).symm

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve
