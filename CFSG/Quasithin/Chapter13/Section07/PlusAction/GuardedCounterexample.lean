module

public import CFSG.Quasithin.ChapterF.Section09.StandingGuard
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.GuardedSource
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.ReducedModule
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.RadicalConjugateRigidity

/-!
# The genuine guarded maximal-counterexample configuration in the plus setup

The original F.9 pair supplies the standing Chapter 3 condition for every
maximal two-local over T. Apply the guarded earlier 3.1.8 theorem to the
actual chosen-module orbits. From any nonquasisimple faithful component,
this constructs a maximal faithful overgroup I, its actual nonzero reduced
commutator U, and the original canonical radical Ξ_p(K)=Ξ_p(I). The proved
13.1.11 rigidity applies to that same radical and normalizer.

Only the genuine guarded 3.1.8 implication remains an earlier-source input;
there is no standing-guard, orbit-bound, rigidity or nonzero-U assumption.
Source: Aschbacher--Smith 13.1.7 setup, 13.1.8(2), 13.1.11, pp.868--872,
in the literal F.9 / 13.7.4 domain, pp.317 and936--937.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction
open Section08.SourceCompletion Chapter1 Chapter12.Section02 Section01
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- F.9.1 discharges the standing condition in the actual chosen-module
consumer of the guarded Chapter 3 theorem. -/
theorem source_orbit_bound_of_guarded318
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    {K W : Subgroup G} (hK : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (D : ChosenModule T K W) : cubicRatio D.orbitRepresentation ≤ 2 :=
  D.orbit_cubicRatio_le_of_guarded_source318 hK.toHypothesis1221 h318
    (fun N hN hTN => h.hasMaximalOutside N hN hTN)

/-- The complete maximal-counterexample opening, with its original radical,
nonzero reduced commutator and proved conjugate rigidity. -/
theorem source_nonquasisimple_counterexample_configuration
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    {K : Subgroup G} (hK : K ∈ nonquasisimpleFaithful T) :
    ∃ I ∈ LStar G T, K ≤ I ∧ FaithfulMaximalLocal T I ∧
      I ∈ nonquasisimpleFaithful T ∧
      IsMaximalTwoLocal (normalizer (I : Set G)) ∧
      IsElementaryAbelian 2 (normalizerMoved I) ∧ normalizerMoved I ≠ ⊥ ∧
      normalizerMoved I ≤ (normalizer (I : Set G)).pCoreIn 2 ∧
      normalizer (normalizerMoved I : Set G) = normalizer (I : Set G) ∧
      (∃ N : Subgroup G, N ∈ Chapter3.HStar (T : Subgroup G) (normalizer (I : Set G))) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧
        p ∣ Nat.card (fittingSubgroup (XiQuotient K)) ∧
        XiP p K ≠ ⊥ ∧ XiP p K = XiP p I ∧
        XiOddQuotient p (XiQuotient (XiP p K)) ∧
        normalizer (XiP p K : Set G) = normalizer (I : Set G) ∧
        ∀ X₁ : Subgroup G, XiP p K ≤ X₁ →
          ∀ hX₁M : X₁ ≤ normalizer (XiP p K : Set G),
            (∀ A : Subgroup (XiFrattiniQuotient (XiP p K)),
              (∀ s : X₁, ∀ a ∈ A,
                xiFrattiniAction X₁ (XiP p K) hX₁M s a ∈ A) → A = ⊥ ∨ A = ⊤) →
            ∀ g : G, X₁ ≤ (normalizer (I : Set G)).conjBy g →
              g ∈ normalizer (I : Set G) ∧
                (normalizer (I : Set G)).conjBy g = normalizer (I : Set G) := by
  obtain ⟨I,hI,hKI,hf,hn,hmax,hjoin,_hu,p,hprime,ho,hp3,hd,hne,he,hNI⟩ :=
    (Chapter14.Section03.FaithfulSource.Counterexample.hypothesis1311 d.counterexample).maximal_counterexample_of_guarded_source318
      h318 (fun N hN hTN => h.hasMaximalOutside N hN hTN) hK
  obtain ⟨hU,hUne,hUcore,hUN⟩ := faithful_maximal_normalizer_moved
    d.counterexample.qtke hf (le_sup_right.trans hjoin)
  have hstar := h.exists_HStar _ hmax (le_sup_right.trans hjoin)
  let : Fact p.Prime := ⟨hprime⟩
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hl := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hK.1 |>.1
  have hq : XiOddQuotient p (XiQuotient (XiP p K)) :=
    (XiP_oddQuotient_of_A36 h36 hl
      (Chapter1.Section02.uniqueness_local_quotient_sqtk d.counterexample.qtke hl.2.2)
      hK.2 ho hd).2
  refine ⟨I,hI,hKI,hf,hn,hmax,hU,hUne,hUcore,hUN,hstar,
    p,hprime,ho,hp3,hd,hne,he,hq,hNI.symm,?_⟩
  intro X₁ hXX₁ hX₁M hirr g hg
  exact RadicalConjugateRigidity.conjugate_eq_of_irreducible ho (XiP p K)
    (normalizer (I : Set G)) X₁
    (isQuasithin_iff_twoLocal.mp d.counterexample.qtke.quasithin _ hmax.1)
    hNI.symm (XiP_isPPerfect p K) hq hXX₁ (hX₁M.trans hNI.ge) hirr g hg

end CFSG.Quasithin.Chapter13.Section07.PlusAction
