module

public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.GuardedPositiveStar.PrimaryRadicals
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.PositiveRadical

/-!
# Solvable-radical centralization on the original maximal counterexample

The complete primary-radical argument applies to the actual maximal
nonquasisimple local component selected from the original F.9 setup.
Its whole solvable radical centralizes R₂(N_G(I)); the standing guard
is supplied by the original pair. No higher exponent, primary kernel,
reduced-module, or Sylow-centralizer input remains.

The genuine universal A.3.12, C.2.7 and guarded 3.1.8 families are the
remaining named earlier source inputs. Source: Aschbacher--Smith
3.2.14, p.585;13.1.4(5),13.1.7, pp.867--869;13.7.4, pp.936--938.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction
open Section08.SourceCompletion Section01 Chapter1 Chapter1.Section02 Chapter12.Section02
open Chapter1.RadicalExclusions.ModelReduction
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

theorem source_counterexample_solvableRadical_centralizes
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hA312 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ →
      ∀ (S : Sylow 2 A) (B : Subgroup A),
        B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (source : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    {K : Subgroup G} (hK : K ∈ nonquasisimpleFaithful T) :
    ∃ I ∈ LStar G (T : Subgroup G), K ≤ I ∧ FaithfulMaximalLocal T I ∧
      I ∈ nonquasisimpleFaithful T ∧
      IsElementaryAbelian 2 (normalizerMoved I) ∧ normalizerMoved I ≠ ⊥ ∧
      (solvableRadical I).map I.subtype ≤ centralizer (normalizerReduced I : Set G) := by
  obtain ⟨I,hI,hKI,hf,hn,_,hU,hUne,_⟩ :=
    source_nonquasisimple_counterexample_configuration d h h318 hK
  have hc := GuardedPositiveStar.maximal_solvableRadical_centralizes_reduced
    d.counterexample.qtke T hA312 source h318
    (fun N hN hTN => h.hasMaximalOutside N hN hTN) hI hn.2
    (normalizer (I : Set G)) I.le_normalizer le_rfl
  rw [← normalizerReduced_eq] at hc
  exact ⟨I,hI,hKI,hf,hn,hU,hUne,hc⟩

end CFSG.Quasithin.Chapter13.Section07.PlusAction
