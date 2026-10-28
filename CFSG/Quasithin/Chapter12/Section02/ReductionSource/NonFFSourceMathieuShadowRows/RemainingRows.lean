module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeExcluded
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.CocodeExclusion

/-!
# The two remaining normalized Mathieu rows

The original quotient is M22 or M24 after the completed M12 and M23
exclusions. In the M22 row, the proved simple marking and original
cocode exclusion retain only code. In the M24 row, the new original
code exclusion selects the actual cocode action of the full automizer.
The original component quotient and orbit are retained together.

This leaves precisely the M22-code exclusion for the final same-orbit
M24-cocode selection; no J4-recognition conclusion is used.
Source: Aschbacher--Smith 8.1.3 and 8.2.9(3), printed pp.713--714,720,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode Atlas.Codes
open MathieuCode.SextetLayers.CoordinateTransport
open Chapter7.NormalizedSource.MathieuShadowRows
open Chapter8.Section02.HermitianSource Chapter8.Section02.MathieuShadowRows
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The remaining normalized rows, preserving the original simple quotient
and the full original automizer in the M24 cocode alternative. -/
theorem sourceOrbit_mathieu_m22_code_or_m24_cocode_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    Nonempty (ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source.MarkedSimpleModel
      D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation) ∨
      (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24) ∧
        ∃ a : Automizer D.sourceOrbit ≃* M24,
          ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode,
            ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
              cocodeRepresentation (a b) (E v)) := by
  have hquotients :
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M22) ∨
        Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24) :=
    sourceOrbit_mathieu_m22_or_m24_of_many (G := G) (T := T) (L := L) (V := V)
      D h hmany hV hm hnon
  refine hquotients.elim ?_ ?_
  · intro h22
    apply Or.inl
    exact (sourceOrbit_m22_simple_marking_of_many (G := G) (T := T) (L := L) (V := V)
      D h hmany hV h22 hnon).resolve_right
        (sourceOrbit_not_m22_cocode_of_many (G := G) (T := T) (L := L) (V := V)
          D h hmany hV hm hnon)
  · intro h24
    exact .inr ⟨h24,D.sourceOrbit_m24_cocode_marking_of_many h hmany hV h24 hnon⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
