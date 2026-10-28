module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.SelectedObstructions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.Source
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Recognized
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeExcluded

/-!
# The remaining doubled obstruction to Proposition 11.3.2

The completed odd-kernel theorem applies to the original nonbinary chosen
module. In the selected overcomponent, the completed Mathieu reduction leaves
the original M22 code, which its source exclusion rules out. Consequently a
counterexample to 11.3.2 supplies an actual non-FF marked doubled orbit in a
faithful maximal overcomponent containing the literal residual O²(H).

The final application requires the doubled exclusion only for these selected
overcomponents. There is no remaining Mathieu, odd-kernel, native-cover or
compatible-field premise. The source flag and preceding geometry remain those
of the original D, so this applies equally to the later swapped-I choice.

This does not prove the doubled exclusion. Its producer is
qt-d-nonff-doubled-short-route; final discharge remains with
qt-d-1222-shadow-linear-geometry and qt-d-1222-natural-shadow-reduction.
The common-core argument retains the q=4 cover obstruction, odd degree,
relative component normality and the two distinct residual conventions.

Source: Aschbacher--Smith, refs/quasithin.pdf, 3.2.5, 4.4.3, 7.0.1,
8.2.13--14 and 11.3.2--9, especially printed pp.770--775.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
open ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- A counterexample selects a genuine non-FF doubled orbit over the original
O²(H). Odd-kernel control and every Mathieu source row are discharged. -/
theorem exists_selected_doubled_of_counterexample
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1132 c f H)
    (hc : ¬ Proposition1132At D S (c.binarySubspace (f.space 0)) H) :
    Source.NormalComponentIn H (residual H) ∧
      ∃ J W : Subgroup G, ∃ E : ChosenModule T J W,
        ComponentSeed T H (residual H) ∧ residual H ≤ J ∧
        J ∈ Chapter1.LStar G (T : Subgroup G) ∧
        J ∈ MainForward.faithfulLocalComponents T ∧
        ¬ J ≤ normalizer (L : Set G) ∧ ⁅sourceZ T,J⁆ ≠ ⊥ ∧
        Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
        E.MarkedDoubled ∧ ¬ IsFFModule E.sourceOrbitNormalizerRepresentation := by
  have hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V) :=
    WeakClosure.Generation.OddNormalizer.oddKernelNormalizer_unconditional D S
  have hdata :=
    exists_selected_nonff_obstruction_of_counterexample (D := D) (S := S) c f hu s p
      hcontrol hc
  obtain ⟨hn,hex⟩ := hdata
  obtain ⟨J,hex⟩ := hex
  obtain ⟨W,hex⟩ := hex
  obtain ⟨E,hex⟩ := hex
  obtain ⟨d,hKJ,hJ,hfaith,hout,hmove,hsrc,hobs⟩ := hex
  obtain ⟨hnon,hcases⟩ := hobs
  rcases hcases with hd | ⟨hW,_,hm⟩
  · exact ⟨hn,J,W,E,d,hKJ,hJ,hfaith,hout,hmove,hsrc,hd,hnon⟩
  · exact (E.sourceOrbit_m22_code_excluded_of_many hsrc S.many hW hnon
      (E.sourceOrbit_mathieu_remaining_m22_code_of_many hsrc S.many hW hnon hm)).elim

/-- The four original source clauses follow from the non-FF doubled exclusion
on maximal overcomponents containing the actual residual. All other inputs
are the original flag and preceding §§11.0--11.2 geometry. -/
theorem proposition1132_of_selected_doubled_exclusion
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1132 c f H)
    (hdoubled : ∀ (J W : Subgroup G) (E : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      residual H ≤ J → J ∈ Chapter1.LStar G (T : Subgroup G) →
      E.MarkedDoubled → ¬ IsFFModule E.sourceOrbitNormalizerRepresentation → False) :
    Proposition1132At D S (c.binarySubspace (f.space 0)) H := by
  classical
  by_contra hc
  obtain ⟨_,hex⟩ :=
    exists_selected_doubled_of_counterexample (D := D) (S := S) c f hu s p hc
  obtain ⟨J,hex⟩ := hex
  obtain ⟨W,hex⟩ := hex
  obtain ⟨E,hex⟩ := hex
  obtain ⟨_,hKJ,hJ,_,_,_,hsrc,hd,hnon⟩ := hex
  exact hdoubled J W E hsrc hKJ hJ hd hnon

/-- Application of the original universal doubled-source contract. Its
multiple-overgroup hypothesis is supplied by the initial nonbinary input. -/
theorem proposition1132_of_doubled_exclusion
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1132 c f H)
    (hdoubled : ∀ (J W : Subgroup G) (E : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      E.MarkedDoubled → ¬ IsFFModule E.sourceOrbitNormalizerRepresentation → False) :
    Proposition1132At D S (c.binarySubspace (f.space 0)) H :=
  proposition1132_of_selected_doubled_exclusion (D := D) (S := S) c f hu s p
    (fun J W E hsrc _ _ => hdoubled J W E hsrc S.many)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
