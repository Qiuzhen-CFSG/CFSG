module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeExcluded
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeSelectionAdapter

/-!
# Same-orbit M24 cocode selection

Excluding the original M22 code through source 8.2.13 leaves the M24 quotient
and full-automizer cocode marking on the unchanged original orbit.
Source: Aschbacher--Smith 8.2.13, printed p.723, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
open Sporadic.Mathieu MathieuCode
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The same original orbit has the M24 quotient and full cocode marking,
with the M22-code alternative discharged from the source hypotheses. -/
theorem sourceOrbit_m24_cocode_selection_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24) ∧
      ∃ a : Automizer D.sourceOrbit ≃* M24,
        ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode,
          ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
            cocodeRepresentation (a b) (E v) :=
  D.sourceOrbit_m24_cocode_selection_of_m22_code_excluded h hmany hV hm hnon
    (D.sourceOrbit_m22_code_excluded_of_many h hmany hV hnon)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
