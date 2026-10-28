module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalSelection
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalFiveAction
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterSourceExits
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.FullCoordinates

/-!
# Fixed-space elimination from the preceding source results

Assume the original C_V(L) is nontrivial. Its literal A₈ quotient and a
fixed involution exclude all unique Sylow-overgroup models, so an actual
H-star subgroup J escapes M. The preceding source classification makes J
solvable or gives the one-or-two A₅ model on [V_J,O²(J)]. Weak closure rules
out the first alternative. In the second, the marked five-point summand
and Borel placement supply the original actor contradiction. Thus C_V(L)
is trivial; the original quotient coordinates become full equivariant
coordinates on the unchanged six-dimensional V.

The same-G,T structural and module conclusions of 12.2.2, earlier A₇
exclusion, and rank-one source exits remain explicit inputs. Their source
producers are the Section02 assembly, qt-d-1231-source (whose D application
retains Hypothesis1311), and qt-d-1222-rankone-module. This conditional
application does not prove those earlier results or infer an unguarded A₇
exclusion from the guarded producer. Every local H-star, Borel, quotient,
summand, evenness and conjugation premise is discharged here.

Source: Aschbacher–Smith, Lemma 12.6.23, printed pp.829–830, using
Corollary 12.3.2 and the preceding 12.6.20–22 arguments.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open CentralLine.LocalContradiction
open Section02
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original fixed-space elimination from the preceding source inputs
at the same G,T. H-star selection and every local action premise are proved. -/
theorem SourceHypothesis.fixed_space_eq_bot_of_source_exits
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : ∀ J : Subgroup G, J ∈ Chapter3.HStar (T : Subgroup G) (M L) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual J) →
      Nonempty ((localResidual J ⧸ pCore 2 (localResidual J)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual J) ∧
        RankOneModule.SmallExit T (localResidual J)) : ZV L V = ⊥ := by
  by_contra hz
  have hs := (structural L H.source).2.2 V H.chosen
  obtain ⟨J,hJ⟩ := H.fixed_exists_hstar D hz
  have hZ := H.fixed_sylow_seed_centralizer_le D hs.1 hz
  rcases Section04.SLThreeCommutatorSource.ConjugateExistence.local_classification_of_source_exits_at
      H.source structural modules hZ hJ seven (exits J hJ) with hsolv | ⟨_,_,hm⟩
  · exact H.fixed_hstar_not_solvable D hs.1 hs.2.2.1 hz hJ hsolv
  · have hm' : Chapter6.Source.IsOneOrTwoA5Modules (localResidual J)
        ⁅localSpan T J,localResidual J⁆ := by
      change Chapter6.Source.IsOneOrTwoA5Modules _
        ⁅Section04.SLThreeCommutatorSource.ConjugateExistence.localModule T J,_⁆
      rw [Section04.SLThreeCommutatorSource.ConjugateExistence.localModule_eq_residual_span hJ.1.1.2]
      exact hm
    exact H.fixed_hstar_not_one_or_two D hs.1 hs.2.2.1 hz hJ hm'

/-- Source 12.6.23's six-dimensional module consequence on the unchanged V,
retaining the original quotient projection and its action marking. -/
theorem SourceHypothesis.fixed_space_and_full_coordinates_of_source_exits
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : ∀ J : Subgroup G, J ∈ Chapter3.HStar (T : Subgroup G) (M L) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual J) →
      Nonempty ((localResidual J ⧸ pCore 2 (localResidual J)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual J) ∧
        RankOneModule.SmallExit T (localResidual J)) :
    ZV L V = ⊥ ∧ Module.finrank (ZMod 2) (Additive V) = 6 ∧
      ∃ E : Additive V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8),
        (∀ v, E v = D.coordinates (Submodule.Quotient.mk v)) ∧
        ∀ (l : L) v, E (seedRepresentation L V H.chosen.normalizes l v) =
          BinaryPermutation.alternatingNaturalRepresentation (Fin 8)
            (D.groupEquiv (QuotientGroup.mk' (conjugation L V H.chosen.normalizes).ker l)) (E v) := by
  have hz := H.fixed_space_eq_bot_of_source_exits D structural modules seven exits
  let E := D.fullLinearCoordinates hz
  refine ⟨hz,E.finrank_eq.trans BinaryPermutation.TerminalOrthogonal.Eight.finrank_natural,
    E,D.fullLinearCoordinates_apply hz,?_⟩
  intro l v
  rw [D.fullLinearCoordinates_apply,D.fullLinearCoordinates_apply]
  exact D.equivariant l (Submodule.Quotient.mk v)

end CFSG.Quasithin.Chapter12.Section06
