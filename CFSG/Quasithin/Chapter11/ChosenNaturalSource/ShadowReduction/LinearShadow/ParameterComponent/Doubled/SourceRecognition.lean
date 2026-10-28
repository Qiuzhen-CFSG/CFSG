module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.RankBudget
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Recognition
public import Theory.Representation.SL2SylowFixedRecognition

/-!
# One natural quotient in the doubled source branch

E-generation and 11.3.5 collapse the actual residual at k=2n. Its compatible
matrix isomorphism, selected Sylow actor, and uniform fixed spaces supply the
inputs to generic G.1.6. The reciprocal rank budget forces multiplicity one.
The proved generic implication from qt-d-1222-shadow-natural-recognition is applied here;
rank-one reduction is owned by qt-d-1222-shadow-rankone-recognition.
The doubled Geometry input and final extension contradiction remain with this
task. These conditional results do not assert the parameter exclusion.

Source: Aschbacher--Smith, 11.3.6, printed pp.772--773.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.SL2SylowFixedRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
open CommonCore CommonCore.NaturalRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {H L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}
    [IsElementaryAbelian 2 (omegaClosure T H)]
    {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The doubled source supplies all hypotheses of G.1.6 at degree 2n.
The earlier rank-one recognition remains an explicit independent input. -/
theorem source_recognition_inputs (s : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (d : Coordinates D S) (z : Geometry d H) (r : RankOneReduction S H)
    (hu : ChapterE.generationParameter H ≤ 2 * S.field.degree)
    (hF : Nat.card F = 2 ^ (2 * S.field.degree)) :
    ∃ (e : residualStar T H ≃* SL(2,F)) (R : Sylow 2 (residualStar T H)) (g : G),
      (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ T ∧
      ¬ (fullModule L V).map (MulAut.conj g).toMonoidHom ≤
        centralizer (omegaClosure T H : Set G) ∧
      (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
        ((((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map
          (starProjection T H)) ∧
      FixedSpaceHypotheses (binaryAction T H e)
        (R.mapSurjective (f := e.toMonoidHom) e.surjective) ∧
      ∀ c : QuotientCoordinates (binaryAction T H e), c.multiplicity = 1 := by
  have hm := (residual_component s d r z.weak_escape z.s_value hu).2
  obtain ⟨g,hg,ha⟩ := exists_active_conjugate s p hc z.weak_escape
  obtain ⟨_,e,_⟩ := compatible_matrix_equivs s hF hm
  obtain ⟨R,hR⟩ := selected_sylow s g d hF hg ha z.s_value hm
  exact ⟨e,R,g,hg,ha,hR,
    doubled_fixedSpaceHypotheses s d hF e R g hg ha z.s_value hm hR,
    fun c => source_multiplicity_one_of_geometry s g d z e hF hg ha hm c R hR⟩

/-- The shared general G.1.6 implication is applied before k=n is proved.
No natural-quotient marking at the later degree n is used. -/
theorem source_one_natural_quotient (s : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (d : Coordinates D S) (z : Geometry d H) (r : RankOneReduction S H)
    (hu : ChapterE.generationParameter H ≤ 2 * S.field.degree)
    (hF : Nat.card F = 2 ^ (2 * S.field.degree)) :
    ∃ (e : residualStar T H ≃* SL(2,F))
      (c : QuotientCoordinates (binaryAction T H e)), c.multiplicity = 1 := by
  obtain ⟨e,R,_,_,_,_,hR,hm⟩ := source_recognition_inputs s p hc d z r hu hF
  obtain ⟨c⟩ := quotientCoordinates_of_fixedSpaceHypotheses
    (binaryAction T H e) (R.mapSurjective (f := e.toMonoidHom) e.surjective) hR
    (2 * S.field.degree) (by have := S.nonbinary; omega) hF
  exact ⟨e,c,hm c⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
