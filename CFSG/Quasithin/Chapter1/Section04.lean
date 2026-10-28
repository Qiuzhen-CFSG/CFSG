module

public import Theory.PGroupCore
public import Theory.Quasithin
public import CFSG.Quasithin.Chapter1.Section04.Source

/-!
# Properties of uniqueness subgroups

The imported `Section04.Source` provides the corrected constructions and
conditional elementary implications for Aschbacher--Smith, §1.4 (combined
manuscript, 1 March 2004, pp. 514--516). Its source premises still need to
be discharged by §§1.1--1.3; clauses (2),(4),(5) also remain to be assembled.

The declarations below are retained as legacy APIs. They do not prove source
Lemma 1.4.1: `K` conflates `L₀` and `L₀T`, `twoCoreM` is unanchored, and the
ambient characteristicness assumption together with the old control condition
forces `M = ⊤`. In particular `lemma_1_4_1_core` is not a source theorem.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.Section04

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- Legacy abstract uniqueness inputs. This is not the setup of Lemma 1.4.1;
use the separately defined constructions in `Section04.Source`. -/
structure UniquenessSetup (G : Type*) [Group G] [Finite G]
    (L T K Q M : Subgroup G) where
  twoCoreM : Subgroup G
  L_le_K : L ≤ K
  T_le_K : T ≤ K
  Q_le_K : Q ≤ K
  Q_ne_bot : Q ≠ ⊥
  Q_is_two : IsPGroup 2 Q
  normalizer_local : IsTwoLocal (normalizer (K : Set G))
  K_le_normalizer : K ≤ normalizer (K : Set G)
  M_maximal : IsMaximalTwoLocal M
  K_le_M : K ≤ M
  normal_in_maximal : ∀ N : Subgroup G, IsMaximalTwoLocal N → K ≤ N →
    (K.subgroupOf N).Normal
  unique_overgroup : ∀ N : Subgroup G, IsMaximalTwoLocal N → K ≤ N → N = M

/-- Legacy ambient-characteristic control, distinct from source `C(G,Q) ≤ M`.
The corrected condition is `Source.ControlsCharacteristicNormalizers`. -/
def ControlsCharacteristicNormalizers {G : Type*} [Group G]
    (Q M : Subgroup G) : Prop :=
  ∀ R : Subgroup G, R ≤ Q → R.Characteristic → R ≠ ⊥ →
    normalizer (R : Set G) ≤ M

/-- The centralizer of a subgroup is contained in its normalizer. -/
private theorem centralizer_le_of_controls
    {G : Type*} [Group G] {Q M : Subgroup G}
    (hQ : Q.Characteristic) (hQne : Q ≠ ⊥)
    (hctrl : ControlsCharacteristicNormalizers Q M) :
    centralizer (Q : Set G) ≤ M := by
  exact (centralizer_le_normalizer (Q : Set G)).trans
    (hctrl Q le_rfl hQ hQne)

/-- Legacy abstract normalizer identification; `K` is not source `L₀T`. -/
public theorem normalizer_eq_unique_of_setup
    {L T K Q M : Subgroup G} (h : UniquenessSetup G L T K Q M) :
  normalizer (K : Set G) = M := by
  have hMle : M ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.K_le_M).mp
      (h.normal_in_maximal M h.M_maximal h.K_le_M)
  apply le_antisymm ?_ hMle
  obtain ⟨N, hnormalizerN, hNmax⟩ :=
    Finite.exists_le_maximal h.normalizer_local
  have hKN : K ≤ N := h.K_le_normalizer.trans hnormalizerN
  have hNM : N = M := h.unique_overgroup N hNmax hKN
  exact hnormalizerN.trans (hNM ▸ le_rfl)

/-- The maximal two-local overgroup containing `K` is unique.  This is the
set-theoretic uniqueness assertion used throughout §1.4. -/
public theorem unique_maximalTwoLocal_overgroup_of_setup
    {L T K Q M : Subgroup G} (h : UniquenessSetup G L T K Q M) :
    {N : Subgroup G | IsMaximalTwoLocal N ∧ K ≤ N} = {M} := by
  ext N
  constructor
  · rintro ⟨hN, hKN⟩
    exact Set.mem_singleton_iff.mpr (h.unique_overgroup N hN hKN)
  · intro hN
    have : N = M := Set.mem_singleton_iff.mp hN
    subst N
    exact ⟨h.M_maximal, h.K_le_M⟩

/-- Legacy centralizer implication with ambient characteristicness. -/
public theorem centralizer_le_unique_of_setup
    {L T K Q M : Subgroup G} (h : UniquenessSetup G L T K Q M)
    (hQchar : Q.Characteristic)
    (hctrl : ControlsCharacteristicNormalizers Q M) :
    centralizer (Q : Set G) ≤ M := by
  exact centralizer_le_of_controls hQchar h.Q_ne_bot hctrl

/-- If `Q` contains the two-core of `M` and `M` has self-centralizing
two-core, then the centralizer of `Q` is contained in `O₂(M)`.  This is the
group-theoretic core of 1.4.1(3). -/
public theorem centralizer_le_twoCore_of_setup
    {L T K Q M : Subgroup G} (h : UniquenessSetup G L T K Q M)
    (hMcore_le_Q : h.twoCoreM ≤ Q)
    (hM_selfcentralizing : centralizer (h.twoCoreM : Set G) ≤ h.twoCoreM) :
    centralizer (Q : Set G) ≤ h.twoCoreM := by
  apply le_trans ?_ hM_selfcentralizing
  intro x hx y hy
  exact hx y (hMcore_le_Q hy)

/-- Legacy identity wrapper. This does not establish source 1.4.1(4). -/
public theorem exists_noncentral_twoSubgroup_of_setup
    {L T K Q M : Subgroup G} (_h : UniquenessSetup G L T K Q M)
    (R₂ : Set (Subgroup G))
    (hfaithful : ∃ V : Subgroup G, V ∈ R₂ ∧ ⁅V, K⁆ ≠ ⊥) :
    ∃ V : Subgroup G, V ∈ R₂ ∧ ⁅V, K⁆ ≠ ⊥ :=
  hfaithful

/-- Legacy package, retained for compatibility. Its assumptions do not encode
the source setup, and it must not be used as source Lemma 1.4.1. -/
public theorem lemma_1_4_1_core
    {L T K Q M : Subgroup G} (h : UniquenessSetup G L T K Q M)
    (hQchar : Q.Characteristic)
    (hctrl : ControlsCharacteristicNormalizers Q M)
    (hMcore_le_Q : h.twoCoreM ≤ Q)
    (hM_selfcentralizing : centralizer (h.twoCoreM : Set G) ≤ h.twoCoreM) :
    normalizer (K : Set G) = M ∧
      {N : Subgroup G | IsMaximalTwoLocal N ∧ K ≤ N} = {M} ∧
      centralizer (Q : Set G) ≤ M ∧
      centralizer (Q : Set G) ≤ h.twoCoreM := by
  exact ⟨normalizer_eq_unique_of_setup h,
    unique_maximalTwoLocal_overgroup_of_setup h,
    centralizer_le_unique_of_setup h hQchar hctrl,
    centralizer_le_twoCore_of_setup h hMcore_le_Q hM_selfcentralizing⟩

end CFSG.Quasithin.Chapter1.Section04
