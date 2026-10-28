module

public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.GuardedPositiveStar.Radicals
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.GuardedCounterexample

/-!
# The canonical positive radical of the actual maximal counterexample

Select the original maximal faithful nonquasisimple component I from the
plus setup. Its original canonical radical Ξ_p(K)=Ξ_p(I) has positive
starred membership, centralizes R₂(N_G(I)), and identifies N_G(I) as the
unique maximal two-local over C_G(Ω₁Z(T)). The F.9 pair discharges the
standing outside-local condition. Every radical and reduced subgroup is
that of the selected source witness.

The genuine universal A.3.12, C.2.7 and guarded 3.1.8 theorems remain
earlier source inputs. Source: Aschbacher--Smith 13.1.4(4--6),13.1.7,
pp.867--869, as needed in 13.7.4, pp.936--938.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction
open Section08.SourceCompletion Section01 Chapter1 Chapter1.Section02 Chapter12.Section02
open Chapter1.RadicalExclusions.ModelReduction
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

theorem source_counterexample_positive_radical
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hA312 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ →
      ∀ (S : Sylow 2 A) (B : Subgroup A),
        B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (source : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    {K : Subgroup G} (hK : K ∈ nonquasisimpleFaithful T) :
    ∃ I ∈ LStar G T, K ≤ I ∧ FaithfulMaximalLocal T I ∧
      I ∈ nonquasisimpleFaithful T ∧
      IsElementaryAbelian 2 (normalizerMoved I) ∧ normalizerMoved I ≠ ⊥ ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧
        XiP p K = XiP p I ∧
        XiP p I ∈ Chapter3.XiPlus G (T : Subgroup G) ∩ XiStar G T ∧
        XiP p I ≤ centralizer (normalizerReduced I : Set G) ∧
        normalizer (XiP p I : Set G) = normalizer (I : Set G) ∧
        IsMaximalTwoLocal (normalizer (I : Set G)) ∧
        centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ normalizer (I : Set G) ∧
        ∀ N : Subgroup G, IsMaximalTwoLocal N →
          centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ N →
          N = normalizer (I : Set G) := by
  obtain ⟨I,hI,hKI,hf,hn,_,hU,hUne,_,_,_,p,hp,ho,hlarge,_,_,he,hq,_⟩ :=
    source_nonquasisimple_counterexample_configuration d h h318 hK
  let : Fact p.Prime := ⟨hp⟩
  have hqi : XiOddQuotient p (XiQuotient (XiP p I)) := he ▸ hq
  have hd := prime_dvd_fitting_of_normal_radical (XiP_le p I)
    (normal_subgroupOf_of_le_normalizer (XiP_invariant p I.le_normalizer)) hqi
  have hstar := GuardedPositiveStar.maximal_radical_positive_star
    d.counterexample.qtke T hA312 source hI hn.2 ho hd
  have hc := GuardedPositiveStar.maximal_radical_reduced_and_centralizer
    d.counterexample.qtke T hA312 source h318
    (fun N hN hTN => h.hasMaximalOutside N hN hTN) hI hn.2 ho hd
  exact ⟨I,hI,hKI,hf,hn,hU,hUne,p,hp,ho,hlarge,he,hstar,hc⟩

end CFSG.Quasithin.Chapter13.Section07.PlusAction
