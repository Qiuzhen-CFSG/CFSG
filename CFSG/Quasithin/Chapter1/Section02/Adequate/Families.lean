module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import CFSG.Quasithin.MainForward.SourceFamilies
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# The canonical local family and its intrinsic module

For an ambient Sylow two-subgroup, Definition 1.2.3 agrees with the family
used in the forward classification reduction. Injectivity of the inclusion
transports nontriviality of the intrinsic two-core to its ambient image.

Condition (E), via 1.1.4(6), makes the join of a local component and the Sylow
subgroup characteristic two. Subnormal inheritance then puts every local
component in the actual family X of A.4.5. Consequently membership in X_f is
detected by the intrinsic module alone. No A.3 classification, maximality,
or centre–Frattini equality is needed for these facts.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Definition 1.2.3 and the discussion preceding Lemma 1.2.9, pp.505–507.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.Adequate
open ChapterA.Section04
variable {G : Type*} [Group G]

/-- The intrinsic and ambient versions of Definition 1.2.3 agree. -/
theorem mem_L_iff_mainForward (T : Sylow 2 G) (B : Subgroup G) :
    B ∈ L G T ↔ B ∈ MainForward.localComponents T := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro he
    apply h.2.2
    change (pCore 2 (B ⊔ (T : Subgroup G) : Subgroup G)).map _ = ⊥
    rw [he, Subgroup.map_bot]
  · intro h
    refine ⟨h.1, ⟨T.subtype le_sup_right, ?_⟩, ?_⟩
    · simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]
    · exact fun he => h.2
        ((map_eq_bot_iff_of_injective _ (B ⊔ (T : Subgroup G)).subtype_injective).mp he)

/-- The faithful family uses precisely the canonical local family and X_f. -/
theorem mem_faithfulLocalComponents_iff (T : Sylow 2 G) (B : Subgroup G) :
    B ∈ MainForward.faithfulLocalComponents T ↔
      B ∈ L G T ∧ IsFaithfulSignalizerType B :=
  and_congr (mem_L_iff_mainForward T B).symm Iff.rfl

variable [Finite G]

/-- Perfect local components have no nontrivial two-group quotient. -/
theorem mem_L_isPPerfect {S B : Subgroup G} (hB : B ∈ L G S) :
    IsPPerfect 2 B := by
  let := mem_L_isPerfect hB
  intro N hn hp
  let := hn
  let := hp.isNilpotent
  exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)

/-- Every canonical local component has self-centralizing two-core, using
only condition (E) at the fixed ambient Sylow subgroup. -/
theorem mem_L_hasCharacteristicTwo (T : Sylow 2 G)
    (hE : IsEvenCharacteristicAt T) {B : Subgroup G} (hB : B ∈ L G T) :
    HasCharacteristicTwo B := by
  have hJ : B ⊔ (T : Subgroup G) ∈ He G :=
    lemma_1_1_4_6 T hE ⟨hB.2.2, show (T : Subgroup G) ≤ B ⊔ T from le_sup_right⟩
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe (show B ≤ B ⊔ (T : Subgroup G) from le_sup_left))).mp
      (subnormal_core_selfCentralizing (mem_He_iff.mp hJ) _ hB.1.subnormal)

/-- The inclusion L(G,T) ⊆ X stated before Lemma 1.2.9. -/
theorem mem_L_isSignalizerType (T : Sylow 2 G)
    (hE : IsEvenCharacteristicAt T) {B : Subgroup G} (hB : B ∈ L G T) :
    IsSignalizerType B := by
  refine ⟨?_, mem_L_isPPerfect hB,
    generalizedFitting_eq_pCore_of_selfCentralizing 2 (mem_L_hasCharacteristicTwo T hE hB)⟩
  intro he
  apply hB.1.ne_bot
  rw [he, bot_subgroupOf]

/-- For local components, the intrinsic module is the only additional
condition for membership in the main reduction's faithful family. -/
theorem mem_faithfulLocalComponents_iff_module (T : Sylow 2 G)
    (hE : IsEvenCharacteristicAt T) {B : Subgroup G} :
    B ∈ MainForward.faithfulLocalComponents T ↔
      B ∈ L G T ∧ intrinsicSignalizerModule B ≠ ⊥ := by
  rw [mem_faithfulLocalComponents_iff]
  exact ⟨fun h => ⟨h.1, h.2.2⟩,
    fun h => ⟨h.1, mem_L_isSignalizerType T hE h.1, h.2⟩⟩

end CFSG.Quasithin.Chapter1.Section02.Adequate
