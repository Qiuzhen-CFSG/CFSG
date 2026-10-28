module

public import CFSG.Quasithin.Chapter13.Section01.RadicalQuotient
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.GuardedCounterexample

/-!
# The PSL₂(p) radical quotient of the actual selected counterexample

The guarded maximal-counterexample construction selects the original I
and constructs U=[R₂(N_G(I)),I]. The completed structural model theorem
now gives I/O∞(I)≅PSL₂(p), p>3, on this same witness. The kernel of the
reduced-module action is not identified with the radical here; that is the
separate original centralizer theorem 13.1.4(5).

Source: Aschbacher--Smith setup of 13.1.7 and 13.1.8, pp.868--869.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction
open Section08.SourceCompletion Section01 Chapter1 Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The selected source counterexample has the required prime-field
rank-one radical quotient, together with its original nonzero module. -/
theorem source_counterexample_radical_quotient
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    {K : Subgroup G} (hK : K ∈ nonquasisimpleFaithful T) :
    ∃ I ∈ LStar G T, K ≤ I ∧ FaithfulMaximalLocal T I ∧
      I ∈ nonquasisimpleFaithful T ∧
      IsElementaryAbelian 2 (normalizerMoved I) ∧ normalizerMoved I ≠ ⊥ ∧
      normalizerMoved I ≤ (normalizer (I : Set G)).pCoreIn 2 ∧
      normalizer (normalizerMoved I : Set G) = normalizer (I : Set G) ∧
      ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ClassicalGroup.IsPSL (I ⧸ solvableRadical I) 2 p := by
  obtain ⟨I,hI,hKI,hf,hn,_,hU,hUne,hUc,hUn,_⟩ :=
    source_nonquasisimple_counterexample_configuration d h h318 hK
  exact ⟨I,hI,hKI,hf,hn,hU,hUne,hUc,hUn,
    nonquasisimple_local_radical_quotient d.counterexample.qtke T hI.1 hn.2⟩

end CFSG.Quasithin.Chapter13.Section07.PlusAction
