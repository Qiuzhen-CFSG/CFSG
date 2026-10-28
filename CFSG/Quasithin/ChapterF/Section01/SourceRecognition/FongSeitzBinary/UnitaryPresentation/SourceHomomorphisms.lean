module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.ModelHomomorphisms
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.SourceEightCells

/-!
# Presentation-constructed maps onto the original unitary source quotient

The literal source equation schemes and generation produce onto maps with
all generator images prescribed. For U₄ the domain is the entire SU₄ model.
For U₅ the domain remains its explicit matrix-generated subgroup until
whole-model generation is proved. These statements keep the original Q.D
quotient, and do not assert scalar descent, Borel equality, or either marked
parabolic comparison. Source: DGS, Theorem D, printed p.224; Steinberg's
Bruhat presentation mechanism, Lectures on Chevalley Groups, Theorems 4/9/33.
-/
public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {E : Type*} [Field E] [CharP E 2]

/-- The exact unitary equations construct an onto SU₄ homomorphism to the
original quotient, with all seven generator families marked. -/
theorem four_original_onto_from_equations [Finite E]
    (Q : SourceQuotient L S) (σ : E ≃+* E) (hσ : Function.Involutive σ)
    (r : PositiveMaps ((generated L S) ⧸ Q.D) (Multiplicative E)
      (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ))
      (Multiplicative E)
      (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ)))
    (cartan : FourWeyl.torusParameters E σ →* ((generated L S) ⧸ Q.D))
    (s t : (generated L S) ⧸ Q.D)
    (heq : (FourPresentation.parameters E σ hσ).Satisfies (Presentation.Generator.ofMaps r cartan s t))
    (hgen : ReflectionLaws.fullGenerated r cartan s t=⊤) :
    ∃ f : (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.form E σ hσ).specialSubgroup →*
        ((generated L S) ⧸ Q.D),
      Function.Surjective f ∧ ∀ j, f (FourPresentation.modelGenerators E σ hσ j)=
        Presentation.Generator.ofMaps r cartan s t j := by
  refine ⟨FourPresentation.lift E σ hσ heq,?_,FourPresentation.lift_generator E σ hσ heq⟩
  apply FourPresentation.lift_surjective E σ hσ heq
  rw [(FourPresentation.parameters E σ hσ).roots_ofMaps heq,
    (FourPresentation.parameters E σ hσ).torus_ofMaps heq]
  exact hgen

/-- The general-q U₅ equations construct the onto map on the actual
matrix-generated subgroup. Whole-SU₅ generation remains explicit in the
choice of this domain and is not claimed by this source application. -/
theorem five_original_generated_onto_from_equations
    (Q : SourceQuotient L S) (J : HermitianForm 5 E) (κ : E)
    (hκ : κ+J.conj κ=1) (hJ : J.form=1)
    (r : PositiveMaps ((generated L S) ⧸ Q.D) (Multiplicative E) (FivePositive.Parameter J)
      (Multiplicative E) (FivePositive.Parameter J))
    (cartan : (Eˣ × Eˣ) →* ((generated L S) ⧸ Q.D)) (s t : (generated L S) ⧸ Q.D)
    (heq : (FivePresentation.parameters J).Satisfies (Presentation.Generator.ofMaps r cartan s t))
    (hgen : ReflectionLaws.fullGenerated r cartan s t=⊤) :
    ∃ f : FivePresentation.matrixGenerated J κ hκ hJ →* ((generated L S) ⧸ Q.D),
      Function.Surjective f ∧ ∀ j, f (FivePresentation.markedGenerator J κ hκ hJ j)=
        Presentation.Generator.ofMaps r cartan s t j := by
  refine ⟨FivePresentation.liftGenerated J κ hκ hJ heq,?_,
    FivePresentation.liftGenerated_generator J κ hκ hJ heq⟩
  apply FivePresentation.liftGenerated_surjective J κ hκ hJ heq
  rw [(FivePresentation.parameters J).roots_ofMaps heq,(FivePresentation.parameters J).torus_ofMaps heq]
  exact hgen
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
