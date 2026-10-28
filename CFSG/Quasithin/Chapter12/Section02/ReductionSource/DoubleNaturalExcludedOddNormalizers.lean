module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerReduction
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerModels
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerComponentModels
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerComplete
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedOddActors

/-!
# The original odd-normalizer reduction and degree-five exclusion

Characteristic abelian reduction, full-orbit odd-core control and the
fixed-residual dichotomy produce an actual pushing-up pair or an actual
outside component with full W-commutator. The completed degree-five
weak-closure/generation argument forces this counterexample directly
from the original doubled branch, with no odd-normalizer callback.

The degree-five argument now excludes the pushing-up pair, including its full
central J₄ cover. Odd-normalizer control follows for every odd-order actor,
and the existing weak-closure and generation arguments give the original
12.1.11 contradiction. The separate degree-four marked-omega implication
in DoubleNaturalExcludedOddActors remains explicit.
Source: Aschbacher--Smith, 4.4.3--12 and 12.1.9--11, pp.619--623,793--794.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  {n : ℕ} (B : DoubledBranch T L V n)

include D h B in
/-- The exact source counterexample after abelian reduction. Either the
covering residual gives an original pushing-up pair, or the odd normalizer
has an outside component moved by the original full doubled orbit. -/
theorem doubledOrbit_oddNormalizer_obstruction
    (hnot : ¬ OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      ((∃ J H : Subgroup G,
        J ∈ muStar (normalizer (L : Set G)) L
          (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
        PushLE L (oddActorResidual L A) J ∧
        IsMaximalTwoLocal H ∧ J ≤ H ∧ ¬ H ≤ normalizer (L : Set G) ∧
        IsSQTK KnownSimple.IsKnownSimple H ∧
        componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
        J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) ∨
      (∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧
        ⁅K,(componentOrbit V (T : Subgroup G)).subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
        pCore 2 K = ⊥ ∧ IsQuasithin K ∧ KnownSimple.IsKnownSimple (K ⧸ center K) ∧
        (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
          normalizer (K : Set (normalizer (A : Set G))) ∧
        (componentOrbit V (T : Subgroup G)).subgroupOf (normalizer (A : Set G)) ≤
          normalizer (K : Set (normalizer (A : Set G))))) := by
  classical
  obtain ⟨X,A,_,hcomm,hne,ho,hA,_,hout⟩ := exists_abelian_of_not_oddNormalizerControl hnot
  let := hcomm
  refine ⟨A.map X.subtype,hne,hcomm,ho,hA,hout,
    (D.doubledOrbit_oddNormalizer_oddCore h B _ hA ho).2,?_⟩
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L (A.map X.subtype)) (normalizer (L : Set G))
  · right
    have hcore := (oddNormalizer_reduction_of_cover_uniqueness D (A.map X.subtype) hu hout).2
    exact D.doubledOrbit_oddNormalizer_full_component h B _ hne hA ho hcore
  · exact Or.inl (D.doubledOrbit_oddNormalizer_pushingUp h _ hA ho hu)


include D h in
/-- The original degree-five branch forces this concrete source counterexample:
the already checked terminal argument rules out odd-normalizer control. -/
theorem doubledFive_oddNormalizer_counterexample_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      ((∃ J H : Subgroup G,
        J ∈ muStar (normalizer (L : Set G)) L
          (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
        PushLE L (oddActorResidual L A) J ∧
        IsMaximalTwoLocal H ∧ J ≤ H ∧ ¬ H ≤ normalizer (L : Set G) ∧
        IsSQTK KnownSimple.IsKnownSimple H ∧
        componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
        J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) ∨
      (∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧
        ⁅K,(componentOrbit V (T : Subgroup G)).subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
        pCore 2 K = ⊥ ∧ IsQuasithin K ∧ KnownSimple.IsKnownSimple (K ⧸ center K) ∧
        (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
          normalizer (K : Set (normalizer (A : Set G))) ∧
        (componentOrbit V (T : Subgroup G)).subgroupOf (normalizer (A : Set G)) ≤
          normalizer (K : Set (normalizer (A : Set G))))) := by
  apply D.doubledOrbit_oddNormalizer_obstruction h B
  intro hodd
  exact D.doubleNatural_five_excluded_of_many_of_odd_control h hmany B hodd

include D h in
/-- Characteristic abelian reduction and the complete placed-model exclusions
leave the original pushing-up pair, an actual outer section, or the normal
J₄ component containing the whole doubled orbit. -/
theorem doubledFive_oddNormalizer_refined_obstruction
    (B : DoubledBranch T L V 5)
    (hnot : ¬ OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      ((∃ J H : Subgroup G,
        J ∈ muStar (normalizer (L : Set G)) L
          (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
        PushLE L (oddActorResidual L A) J ∧
        IsMaximalTwoLocal H ∧ J ≤ H ∧ ¬ H ≤ normalizer (L : Set G) ∧
        IsSQTK KnownSimple.IsKnownSimple H ∧
        componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
        J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) ∨
      (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
        ∃ K : Subgroup (normalizer (A : Set G)),
          IsComponent (normalizer (A : Set G)) K ∧
          ⁅K,(componentOrbit V (T : Subgroup G)).subgroupOf (normalizer (A : Set G))⁆ = K ∧
          ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
          pCore 2 K = ⊥ ∧ FiveNormalizerComponentCases L (componentOrbit V (T : Subgroup G)) A K)) := by
  classical
  obtain ⟨X,A,_,hcomm,hne,ho,hA,_,hout⟩ := exists_abelian_of_not_oddNormalizerControl hnot
  let := hcomm
  refine ⟨A.map X.subtype,hne,hcomm,ho,hA,hout,
    (D.doubledOrbit_oddNormalizer_oddCore h B _ hA ho).2,?_⟩
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L (A.map X.subtype)) (normalizer (L : Set G))
  · exact Or.inr ⟨hu,D.doubledFive_oddNormalizer_component_of_unique h B _ hne hA ho hu hout⟩
  · exact Or.inl (D.doubledOrbit_oddNormalizer_pushingUp h _ hA ho hu)

include D h in
/-- The original degree-five branch produces the refined source obstruction
with no assumed odd-normalizer control or component-classification input. -/
theorem doubledFive_refinedOddNormalizer_counterexample_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      ((∃ J H : Subgroup G,
        J ∈ muStar (normalizer (L : Set G)) L
          (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
        PushLE L (oddActorResidual L A) J ∧
        IsMaximalTwoLocal H ∧ J ≤ H ∧ ¬ H ≤ normalizer (L : Set G) ∧
        IsSQTK KnownSimple.IsKnownSimple H ∧
        componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
        J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) ∨
      (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
        ∃ K : Subgroup (normalizer (A : Set G)),
          IsComponent (normalizer (A : Set G)) K ∧
          ⁅K,(componentOrbit V (T : Subgroup G)).subgroupOf (normalizer (A : Set G))⁆ = K ∧
          ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
          pCore 2 K = ⊥ ∧ FiveNormalizerComponentCases L (componentOrbit V (T : Subgroup G)) A K)) := by
  apply D.doubledFive_oddNormalizer_refined_obstruction h B
  intro hodd
  exact D.doubleNatural_five_excluded_of_many_of_odd_control h hmany B hodd

include D h in
/-- The original degree-five branch forces the actual pushing-up alternative.
All outer sections and the normal J₄ component are excluded, without an
odd-normalizer or component-classification callback. -/
theorem doubledFive_oddNormalizer_pushingUp_counterexample_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
      ∃ J H : Subgroup G,
        J ∈ muStar (normalizer (L : Set G)) L
          (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
        PushLE L (oddActorResidual L A) J ∧
        IsMaximalTwoLocal H ∧ J ≤ H ∧ ¬ H ≤ normalizer (L : Set G) ∧
        IsSQTK KnownSimple.IsKnownSimple H ∧
        componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
        J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L := by
  have hnot : ¬ OddNormalizerControl (componentOrbit V (T : Subgroup G))
      (normalizer (L : Set G)) :=
    fun hodd => D.doubleNatural_five_excluded_of_many_of_odd_control h hmany B hodd
  obtain ⟨X,A,_,hcomm,hne,ho,hA,_,hout⟩ := exists_abelian_of_not_oddNormalizerControl hnot
  let := hcomm
  have hu : ¬ UniqueMaximalOvergroup (oddActorResidual L (A.map X.subtype))
      (normalizer (L : Set G)) := fun hu =>
    hout (D.doubledFive_oddNormalizer_control_of_unique_of_many h hmany B _ hne hA ho hu)
  exact ⟨A.map X.subtype,hne,hcomm,ho,hA,hout,hu,
    D.doubledOrbit_oddNormalizer_pushingUp h _ hA ho hu⟩

include D h in
/-- Source 12.1.11 excludes the original degree-five doubled branch, with all
odd-normalizer, actor, centralizer, weak-closure and generation inputs discharged. -/
theorem doubleNatural_five_excluded_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) : False :=
  D.doubleNatural_five_excluded_of_many_of_odd_control h hmany B
    (D.doubledFive_oddNormalizer_control_of_many h hmany B)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
