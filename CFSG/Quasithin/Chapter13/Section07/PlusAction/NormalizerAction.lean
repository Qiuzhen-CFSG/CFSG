module
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.NormalizerAction.Supplement
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.SolvableRadical

/-!
# Original 13.1.8 for the F.9 maximal counterexample

The original NaturalSetup and F.9 pair select the same maximal faithful
nonquasisimple component I. Its literal normalizer quotient has faithful
conjugation action, and the I-image is PSL₂(p), p>3, with kernel O∞(I).
Every radical supplement gives the same nonzero reduced commutator.
The F.9 pair supplies the standing guard; A.3.12, C.2.7 and guarded
3.1.8 remain genuine earlier source families.

Source: Aschbacher--Smith 13.1.8, pp.868--869, as needed in the
13.7.4 component elimination, pp.936--938.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction
open Section08.SourceCompletion Section01 Chapter1 Chapter1.Section02 Chapter12.Section02
open Chapter1.RadicalExclusions.ModelReduction
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

theorem source_counterexample_normalizer_action
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
      (NormalizerReducedAction.componentMap I).ker = solvableRadical I ∧
      I ⊓ centralizer (normalizerReduced I : Set G) = (solvableRadical I).map I.subtype ∧
      (∃ p : ℕ, p.Prime ∧ 3 < p ∧
        ClassicalGroup.IsPSL (NormalizerReducedAction.componentImage I) 2 p) ∧
      Function.Injective (NormalizerReducedAction.action I) ∧
      normalizerMoved I ≠ ⊥ ∧
      ∀ I₁ : Subgroup G, (solvableRadical I).map I.subtype ⊔ I₁ = I →
        ⁅normalizerReduced I,I₁⁆ = normalizerMoved I ∧
        ∃ p : ℕ, p.Prime ∧ 3 < p ∧
          ClassicalGroup.IsPSL (I₁ ⧸ solvableRadical I₁) 2 p := by
  obtain ⟨I,hI,hKI,hf,hn,_,_,_⟩ :=
    source_counterexample_solvableRadical_centralizes d h hA312 source h318 hK
  obtain ⟨hk,hc,hm,hne,hgen⟩ := maximal_nonquasisimple_normalizer_action
    d.counterexample.qtke T hA312 source h318
    (fun N hN hTN => h.hasMaximalOutside N hN hTN) hf hn.2
  obtain ⟨p,hp,hp3,hmodel⟩ := hm
  refine ⟨I,hI,hKI,hf,hn,hk,hc,⟨p,hp,hp3,hmodel⟩,
    NormalizerReducedAction.action_injective I,hne,?_⟩
  intro I₁ hsup
  have hI₁I : I₁ ≤ I := hsup ▸ le_sup_right
  exact ⟨hgen I₁ hsup,p,hp,hp3,hmodel.of_mulEquiv
    (NormalizerReducedAction.supplementQuotientEquiv hI₁I hk hsup)⟩

end CFSG.Quasithin.Chapter13.Section07.PlusAction
