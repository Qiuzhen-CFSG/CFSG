module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.Setup
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.Chapter4.Section04.OddActorLargeComponent
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.Models

/-!
# Odd-core control and the moved component for the nonbinary module

The original T-normalized V has its full normalizer in N(L). Its order is
at least 64, so 4.4.8 centralizes the odd core of N(A) and puts that core
in N(L). In the trivial-two-core branch the generalized-Fitting argument
constructs a component moved by this same V, outside N(L). The component
has its actual Theorem B central-quotient model and is normalized by the
original fixed residual. No inner-action or normal-component premise is
assumed; those later steps remain to be proved.

Source: Aschbacher--Smith, 4.4.7--10, printed pp.620--621.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

theorem module_normalizer_le : normalizer (V : Set G) ≤ normalizer (L : Set G) :=
  D.normal_subgroup_normalizer_le S.source.toHypothesis1221
    (D.le_component.trans le_sup_left) D.ne_bot (sup_le D.normalizes S.sylow_normalizes)

theorem component_sylow_unique :
    UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) := by
  have hu := S.source.toHypothesis1221.sylow_normalized_maximal_unique
    D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  exact ⟨hu.1, sup_le L.le_normalizer D.sylow_normalizes_component, hu.2⟩

omit D S in
theorem odd_card_of_elementary {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hAe : IsElementaryAbelian p A) : Odd (Nat.card A) := by
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
  rw [hn]
  exact ho.pow

theorem oddCore_control {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (ho : Odd (Nat.card A)) :
    ⁅V, (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype⁆ = ⊥ ∧
    (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤
      normalizer (L : Set G) := by
  have hc := chosen_oddNormalizer_centralizes_oddCore_of_large_module
    S.source.toHypothesis1221 D (lt_of_lt_of_le (by decide) (module_card_ge D S)) A
    (hA.trans inf_le_left) (actor_commutator D S hA) ho (hA.trans inf_le_right)
  exact ⟨hc, (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
    ((Subgroup.centralizer_le_normalizer _).trans (module_normalizer_le D S))⟩

theorem reductions {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G)) :
    normalizer (A : Set G) ≠ ⊤ ∧ IsQuasithin (normalizer (A : Set G)) ∧
    IsKGroup KnownSimple.IsKnownSimple (normalizer (A : Set G)) ∧
    V ≤ (normalizer (L : Set G) ⊓ normalizer (A : Set G)).pCoreIn 2 ∧
    ⁅V, (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype⁆ = ⊥ ∧
    (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤
      normalizer (L : Set G) := by
  let := hAe
  have hodd := odd_card_of_elementary hp ho A hAe
  obtain ⟨hn,hqt,hkg⟩ := oddNormalizer_properQTK S.source.simpleQTKE A hne
  exact ⟨hn,hqt,hkg,chosen_oddNormalizer_module_le_intersection_core
    S.source.toHypothesis1221 D A (hA.trans inf_le_left)
      (actor_commutator D S hA) hodd (hA.trans inf_le_right),oddCore_control D S hA hodd⟩

theorem component_of_core_eq_bot {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hcore : pCore 2 (normalizer (A : Set G)) = ⊥) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      V.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) := by
  let := hAe
  have hodd := odd_card_of_elementary hp ho A hAe
  have hc := actor_commutator D S hA
  obtain ⟨K,hK,hm,hout,hcoreK,hqt,_⟩ :=
    chosen_oddNormalizer_exists_moved_component_of_large_module S.source.toHypothesis1221 D
      (lt_of_lt_of_le (by decide) (module_card_ge D S)) A hne (hA.trans inf_le_left)
      hc hodd (hA.trans inf_le_right) hcore
  obtain ⟨_,hFK,hVK⟩ := chosen_oddNormalizer_component_normalization
    S.source.toHypothesis1221 D A (hA.trans inf_le_left) hc hodd (hA.trans inf_le_right) K hK
  let : IsQuasisimple K := hK.2
  have hkg : IsKGroup KnownSimple.IsKnownSimple K :=
    ((oddNormalizer_properQTK S.source.simpleQTKE A hne).2.2).subgroup K
  exact ⟨K,hK,hK.commutator_eq_self_of_normalizes hVK hm,hout,hcoreK,
    ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
      ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple hqt hkg,hFK,hVK⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
