module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.Setup
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.PointSylow.MarkedOrbit
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.Chapter4.Section04.OddActorCounterexample
public import CFSG.Quasithin.Chapter4.Section04.OddActorLargeComponent
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.Models

/-!
# Original exterior odd-normalizer reductions

The aligned marking supplies N(V) ≤ M. The actual module has order 1024,
so the large-module odd-core argument gives [V,O(N(A))] = 1 and O(N(A)) ≤ M.
This proves the odd-core step without a pushing-up uniqueness assumption.
For a nontrivial elementary odd actor, its normalizer is a proper QTK group,
and V lies in the two-core of its literal intersection with M.

An outside normalizer then yields either the actual maximal pushing-up pair
or a component moved by V, with its full Theorem B model and the original
residual action. Neither branch is excluded here. In particular, this is
not yet a constructor of ExteriorOddNormalizerControl: the specialized
4.2.13 analysis and the 4.4.10--12 and J₄ endgame remain to be proved.

Source: Aschbacher--Smith, 12.2.11(a), pp.798--799; 4.4.5--10, pp.620--621.
The J₄ terminal argument is on p.623.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The marked T-invariance supplies normalizer control for the original V. -/
theorem exterior_module_normalizer_le (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    normalizer (V : Set G) ≤ s.marking.M :=
  D.normal_subgroup_normalizer_le h.toHypothesis1221
    (D.le_component.trans le_sup_left) D.ne_bot s.normalizes

/-- Ordinary source uniqueness over LT, not over the smaller fixed residual. -/
theorem exterior_component_sylow_unique (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) s.marking.M := by
  have hu := h.toHypothesis1221.sylow_normalized_maximal_unique
    D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  exact ⟨hu.1, sup_le L.le_normalizer D.sylow_normalizes_component, hu.2⟩

/-- The complete odd-core step for the exterior module on the literal N(A). -/
theorem exterior_oddNormalizer_oddCore_control (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hAM : A ≤ s.marking.M) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G)) :
    ⁅V, (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype⁆ = ⊥ ∧
    (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤
      s.marking.M := by
  have hc := chosen_oddNormalizer_centralizes_oddCore_of_large_module
    h.toHypothesis1221 D (by rw [s.marking.card_module]; decide) A hAM
    (s.marking.centralizing_actor_commutator hAM hAV) hodd hAV
  exact ⟨hc, (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
    ((Subgroup.centralizer_le_normalizer _).trans (exterior_module_normalizer_le s h))⟩

private theorem odd_card_of_elementary {p : ℕ} (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hAe : IsElementaryAbelian p A) : Odd (Nat.card A) := by
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
  rw [hn]
  exact (hp.odd_of_ne_two (by omega)).pow

/-- The literal prime-actor hypotheses discharge all odd-core setup inputs. -/
theorem exterior_oddNormalizer_reductions (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G)) :
    normalizer (A : Set G) ≠ ⊤ ∧
    IsQuasithin (normalizer (A : Set G)) ∧
    IsKGroup KnownSimple.IsKnownSimple (normalizer (A : Set G)) ∧
    V ≤ (s.marking.M ⊓ normalizer (A : Set G)).pCoreIn 2 ∧
    ⁅V, (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype⁆ = ⊥ ∧
    (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤
      s.marking.M := by
  let := hAe
  have ho := odd_card_of_elementary hp hpgt A hAe
  obtain ⟨hn, hqt, hkg⟩ := oddNormalizer_properQTK h.simpleQTKE A hne
  exact ⟨hn, hqt, hkg,
    chosen_oddNormalizer_module_le_intersection_core h.toHypothesis1221 D A hAM
      (s.marking.centralizing_actor_commutator hAM hAV) ho hAV,
    exterior_oddNormalizer_oddCore_control s h A hAM ho hAV⟩

/-- In the trivial-two-core branch, construct the actual moved component and model. -/
theorem exterior_oddNormalizer_component_of_core_eq_bot (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hcore : pCore 2 (normalizer (A : Set G)) = ⊥) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
      pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      V.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) := by
  let := hAe
  have ho := odd_card_of_elementary hp hpgt A hAe
  have hc := s.marking.centralizing_actor_commutator hAM hAV
  obtain ⟨K, hK, hm, hout, hcoreK, hqt, _⟩ :=
    chosen_oddNormalizer_exists_moved_component_of_large_module h.toHypothesis1221 D
      (by rw [s.marking.card_module]; decide) A hne hAM hc ho hAV hcore
  obtain ⟨_, hFK, hVK⟩ := chosen_oddNormalizer_component_normalization
    h.toHypothesis1221 D A hAM hc ho hAV K hK
  let : IsQuasisimple K := hK.2
  have hkg : IsKGroup KnownSimple.IsKnownSimple K :=
    ((oddNormalizer_properQTK h.simpleQTKE A hne).2.2).subgroup K
  exact ⟨K, hK, hK.commutator_eq_self_of_normalizes hVK hm, hout, hcoreK,
    ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
      ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple
      hqt hkg, hFK, hVK⟩

/-- Failure of odd-normalizer control exposes the actual pushing-up obstruction. -/
theorem exterior_oddNormalizer_pushingUp_or_core_eq_bot (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    (∃ J H : Subgroup G,
      J ∈ muStar s.marking.M L (coveringOvergroup s.marking.M L (oddActorResidual L A)) ∧
      PushLE L (oddActorResidual L A) J ∧
      IsMaximalTwoLocal H ∧ J ≤ H ∧ ¬ H ≤ s.marking.M ∧
      IsSQTK KnownSimple.IsKnownSimple H ∧ V ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn s.marking.M L ∧
      let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      (L : Set G) = (LH : Set G) * (L.pCoreIn 2 : Set G) ∧
      LH ≤ H ⊓ s.marking.M ∧ (LH.subgroupOf (H ⊓ s.marking.M)).Normal ∧
      V = ⁅V, LH⁆ ∧ V ≤ LH) ∨
    pCore 2 (normalizer (A : Set G)) = ⊥ := by
  classical
  have ho := odd_card_of_elementary hp hpgt A hAe
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M
  · exact Or.inr (oddNormalizer_reduction_of_cover_uniqueness D A hu hout).2
  · exact Or.inl (chosen_oddActorResidual_source_counterexample h.toHypothesis1221 D
      A hAM (s.marking.centralizing_actor_commutator hAM hAV) ho hAV
      (exterior_component_sylow_unique s h) hu)

/-- The original exterior hypotheses construct both source branches. No
normalizer control, residual uniqueness or component model is assumed. -/
theorem exterior_oddNormalizer_outside_alternatives (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    (∃ J H : Subgroup G,
      J ∈ muStar s.marking.M L (coveringOvergroup s.marking.M L (oddActorResidual L A)) ∧
      PushLE L (oddActorResidual L A) J ∧
      IsMaximalTwoLocal H ∧ J ≤ H ∧ ¬ H ≤ s.marking.M ∧
      IsSQTK KnownSimple.IsKnownSimple H ∧ V ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn s.marking.M L ∧
      let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      (L : Set G) = (LH : Set G) * (L.pCoreIn 2 : Set G) ∧
      LH ≤ H ⊓ s.marking.M ∧ (LH.subgroupOf (H ⊓ s.marking.M)).Normal ∧
      V = ⁅V, LH⁆ ∧ V ≤ LH) ∨
    (∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
      pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      V.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G)))) := by
  rcases exterior_oddNormalizer_pushingUp_or_core_eq_bot s h p hp hpgt A hAe hAM hAV hout
    with hpair | hcore
  · exact Or.inl hpair
  · exact Or.inr (exterior_oddNormalizer_component_of_core_eq_bot
      s h p hp hpgt A hne hAe hAM hAV hcore)

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
