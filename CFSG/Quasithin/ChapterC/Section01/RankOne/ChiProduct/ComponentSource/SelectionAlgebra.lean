module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.CyclicIntersection
public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.Source
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent

/-!
# Actual seed and component selection in B.1.13

The source local commutator identity supplies a single best offender moving
the seed. B.1.10 then centralizes the Fitting subgroup. If every component
were also centralized, generalized-Fitting self-centralization would put the
seed in Z(F(G)); otherwise the component commutator dichotomy selects a moved
component normalized by the actual offender subgroup.

Source: Aschbacher--Smith B.1.13, printed p.73.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
open ChapterB ComponentRecognition
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [FiniteDimensional (ZMod 2) V] in
/-- One original best offender already generates the seed by commutators. -/
theorem exists_bestOffender_seed_commutator (K T : Subgroup G)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal)
    (hcomm : K = ⁅K, generatedBy {A | IsBestOffender ρ A} T⁆) :
    ∃ A, IsBestOffender ρ A ∧ A ≤ T ∧ K = ⁅K,A⁆ := by
  have hne : K ≠ ⊥ := by
    rcases hkind with hq | h3
    · let := hq
      let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
      exact (nontrivial_iff_ne_bot K).mp ((QuotientGroup.mk'_surjective (center K)).nontrivial)
    · intro he; rw [he, card_bot] at h3; omega
  obtain ⟨A, hA, hAT, hactive⟩ : ∃ A, IsBestOffender ρ A ∧ A ≤ T ∧ ⁅K,A⁆ ≠ ⊥ := by
    by_contra! hn
    apply hne
    rw [hcomm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    exact iSup_le fun A => iSup_le fun hA => le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (hn A hA.1 hA.2))
  have hAJ : A ≤ generatedBy {B | IsBestOffender ρ B} T :=
    le_iSup_of_le A (le_iSup_of_le ⟨hA,hAT⟩ le_rfl)
  have hCK : ⁅K,A⁆ ≤ K := (commutator_mono le_rfl hAJ).trans hcomm.symm.le
  refine ⟨A,hA,hAT,?_⟩
  rcases hkind with hq | h3
  · let := hq
    let H := K ⊔ T
    have hKH : K ≤ H := le_sup_left
    have hAH : A ≤ H := hAT.trans le_sup_right
    have hcomp : IsComponent H (K.subgroupOf H) :=
      ⟨hK, IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hKH).symm⟩
    have hm : (⁅K.subgroupOf H,A.subgroupOf H⁆).map H.subtype = ⁅K,A⁆ := by
      rw [map_commutator, map_subgroupOf_eq_of_le hKH, map_subgroupOf_eq_of_le hAH]
    rcases hcomp.commutator_dichotomy (A.subgroupOf H) with hb | he
    · exact (hactive (by rw [← hm,hb,Subgroup.map_bot])).elim
    · apply le_antisymm ?_ hCK
      have hh := map_mono (f := H.subtype)
        ((le_iSup_conjugates (K.subgroupOf H) (A.subgroupOf H)).trans he.symm.le)
      simpa only [map_subgroupOf_eq_of_le hKH, hm] using hh
  · have hd := card_dvd_of_le hCK
    rw [h3] at hd
    have hc : Nat.card (⁅K,A⁆ : Subgroup G) = 3 :=
      ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left
        (fun he => hactive (card_eq_one.mp he))
    exact (eq_of_le_of_card_ge hCK (by rw [h3,hc])).symm

/-- The original moved local seed centralizes the actual Fitting subgroup. -/
theorem moved_seed_centralizes_fitting (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (K T : Subgroup G)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal)
    (hcomm : K = ⁅K, generatedBy {A | IsBestOffender ρ A} T⁆) :
    K ≤ centralizer (fittingSubgroup G : Set G) := by
  obtain ⟨A,hA,_,hKA⟩ := exists_bestOffender_seed_commutator ρ K T hkind hK hcomm
  exact (source_lemma_B_1_10 ρ hf hcore K A hkind hA hKA).trans inf_le_right

/-- The genuine component-selection alternative preceding B.1.13's model
inspection. The cubic central case retains Z(F(G)) as an actual subgroup. -/
theorem central_fitting_or_moved_component (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) (K T : Subgroup G)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal)
    (hcomm : K = ⁅K, generatedBy {A | IsBestOffender ρ A} T⁆) :
    (Nat.card K = 3 ∧ K ≤ (center (fittingSubgroup G)).map (fittingSubgroup G).subtype) ∨
    ∃ L, IsComponent G L ∧ ⁅L,K⁆ = L := by
  have hKF := moved_seed_centralizes_fitting ρ hf hcore K T hkind hK hcomm
  by_cases hz : K ≤ (center (fittingSubgroup G)).map (fittingSubgroup G).subtype
  · left
    refine ⟨?_,hz⟩
    rcases hkind with hq | h3
    · let := hq
      let : Group.IsSolvable ((center (fittingSubgroup G)).map (fittingSubgroup G).subtype) :=
        Group.isSolvable_of_surjective ((fittingSubgroup G).subtype.subgroupMap_surjective _)
      let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective (f := inclusion hz) (inclusion_injective hz)
      let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
      let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
      exact (Group.IsPerfect.not_isSolvable K inferInstance).elim
    · exact h3
  · right
    obtain ⟨L,hL,hm⟩ : ∃ L, IsComponent G L ∧ ⁅L,K⁆ ≠ ⊥ := by
      by_contra! hn
      have hEC : componentLayer G ≤ centralizer (K : Set G) :=
        sSup_le fun L hL => commutator_eq_bot_iff_le_centralizer.mp (hn L hL)
      have hKC : K ≤ centralizer (generalizedFitting G : Set G) := by
        apply le_centralizer_iff.mpr
        exact sup_le (le_centralizer_iff.mp hKF) hEC
      have hKin := hKC.trans centralizer_generalizedFitting_le_fitting
      apply hz
      intro k hk
      refine ⟨⟨k,hKin hk⟩, ?_,rfl⟩
      exact mem_center_iff.mpr fun x => Subtype.ext (hKF hk x x.property)
    refine ⟨L,hL, hL.commutator_eq_self_of_normalizes ?_ hm⟩
    exact (le_offenderSubgroup_of_local_commutator ρ K T hcomm).trans
      (offenderSubgroup_le_normalizer_component ρ hf hL)

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
