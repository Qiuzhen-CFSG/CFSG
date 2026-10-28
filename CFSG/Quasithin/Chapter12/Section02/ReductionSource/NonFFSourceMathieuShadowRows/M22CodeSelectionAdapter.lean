module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.RemainingRows

/-!
# Conditional same-orbit M24 cocode selection

The preceding normalized rows leave the original simple M22 code or the
original M24 quotient with its full-automizer code/cocode marking.  This small
adapter records the exact final transport step used after the independent
M22-code exclusion: the surviving quotient is M24 and the marking is the
literal cocode on `D.sourceOrbit`.

The M22-code exclusion is deliberately an explicit premise here.  The
unconditional source theorem belongs to the owner that proves the printed
8.2.2--8.2.13 argument and must discharge that premise in its final assembly.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option backward.isDefEq.respectTransparency false in
/-- Once the original M22-code marking is excluded, the unchanged original
orbit carries the actual M24 quotient and full-automizer cocode action. -/
theorem sourceOrbit_m24_cocode_selection_of_m22_code_excluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hm22 : ¬ Nonempty (M22Source.MarkedSimpleModel D.orbitRepresentation
      D.orbitComponent m22OuterCodeRepresentation)) :
    Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24) ∧
      ∃ a : ChapterE.Automizer D.sourceOrbit ≃* M24,
        ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode,
          ∀ b v, E (ChapterE.automizerRepresentation D.sourceOrbit b v) =
            cocodeRepresentation (a b) (E v) := by
  have hrows := sourceOrbit_mathieu_m22_code_or_m24_cocode_of_many
    (G := G) (T := T) (L := L) (V := V) D h hmany hV hm hnon
  rcases hrows with h22 | ⟨h24, a, E, hE⟩
  · exact (hm22 h22).elim
  · exact ⟨h24, a, E, hE⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
