module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonbinaryNaturalInput
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerSetup
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# The common source setup for the nonbinary Sylow normalizer

The original chosen module supplies T-invariance of L. Source uniqueness
then controls the normalizer of LT and of the chosen V, without any fixed-space
or structural-classification premise. Schur--Zassenhaus supplies the actual
odd complement in N_G(T). If two T-invariant subgroups generate LT, an escaping
complement must move one of them. The common-normal theorem makes the join
with either minimal parabolic a genuine local overgroup.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
3.3.4--6, 3.3.10(1), 3.3.15--16, printed pp.586--591.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
open CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The source Hall complement is an actual subgroup of N_G(T). -/
structure OddSupplement (T : Sylow 2 G) where
  subgroup : Subgroup G
  normalizes : subgroup ≤ normalizer (T : Set G)
  odd : Odd (Nat.card subgroup)
  disjoint : Disjoint (T : Subgroup G) subgroup
  generate : (T : Subgroup G) ⊔ subgroup = normalizer (T : Set G)

/-- No solvability or classification assumption is needed to split the normal
Sylow subgroup inside its own normalizer. -/
theorem oddSupplement_nonempty (T : Sylow 2 G) : Nonempty (OddSupplement T) := by
  let N := normalizer (T : Set G)
  let P : Sylow 2 N := T.subtype (T : Subgroup G).le_normalizer
  let : (P : Subgroup N).Normal := normal_in_normalizer
  obtain ⟨A, hA⟩ := exists_right_complement'_of_coprime P.card_coprime_index
  have hP : (P : Subgroup N).map N.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le (T : Subgroup G).le_normalizer
  refine ⟨⟨A.map N.subtype, map_subtype_le _, ?_, ?_, ?_⟩⟩
  · rw [card_map_of_injective N.subtype_injective, ← hA.symm.index_eq_card]
    exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using P.not_dvd_index)
  · rw [← hP]
    exact disjoint_map N.subtype_injective hA.disjoint
  · rw [← hP, ← Subgroup.map_sup, hA.sup_eq_top, ← MonoidHom.range_eq_map,
      range_subtype]

include D S

/-- Uniqueness controls the literal LT normalizer, without asserting that
N_G(L) preserves the particular Sylow subgroup. -/
theorem join_normalizer_le :
    normalizer ((L ⊔ (T : Subgroup G) : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  let J := L ⊔ (T : Subgroup G)
  have hne : J.pCoreIn 2 ≠ ⊥ :=
    fun hz => D.ne_bot (bot_unique (D.le_core.trans_eq hz))
  exact (normalizer_le_normalizer_characteristic_image J (pCore 2 J)).trans
    (D.normal_subgroup_normalizer_le S.source.toHypothesis1221
      (map_subtype_le _) hne
      (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))))

/-- The actual normalized seed already has its full normalizer in N_G(L).
This uses neither global TI nor a nonzero fixed subgroup. -/
theorem seed_normalizer_le : normalizer (V : Set G) ≤ normalizer (L : Set G) :=
  D.normal_subgroup_normalizer_le S.source.toHypothesis1221
    (D.le_sylow.trans le_sup_right) D.ne_bot (sup_le D.normalizes S.sylow_normalizes)

namespace OddSupplement
variable {D S} (A : OddSupplement T)

omit S [Finite G] in
/-- Source 3.3.6(a), for this literal odd complement. -/
theorem escapes (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ¬ A.subgroup ≤ normalizer (L : Set G) := by
  intro hA
  exact hescape (A.generate ▸ sup_le D.sylow_normalizes_component hA)

/-- The common two-core obstruction applies to the same odd complement. -/
theorem join_core_eq_bot
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ((L ⊔ (T : Subgroup G)) ⊔ A.subgroup).pCoreIn 2 = ⊥ :=
  join_core_eq_bot_of_escape S.source D (A.escapes (D := D) hescape)

/-- Source 3.3.15's generation step: an escaping complement moves at least
one of two subgroups generating the original local join with T. -/
theorem moves_generator {Y₁ Y₂ : Subgroup G}
    (hgen : (Y₁ ⊔ Y₂) ⊔ (T : Subgroup G) = L ⊔ (T : Subgroup G))
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ¬ A.subgroup ≤ normalizer (Y₁ : Set G) ∨
      ¬ A.subgroup ≤ normalizer (Y₂ : Set G) := by
  by_contra! hn
  have hY : A.subgroup ≤ normalizer ((Y₁ ⊔ Y₂ : Subgroup G) : Set G) :=
    (le_inf hn.1 hn.2).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJ : A.subgroup ≤ normalizer ((L ⊔ (T : Subgroup G) : Subgroup G) : Set G) := by
    rw [← hgen]
    exact (le_inf hY A.normalizes).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact A.escapes (D := D) hescape (hJ.trans (join_normalizer_le D S))

/-- Source 3.3.10(1) gives a genuine local group for each supplied minimal
parabolic, with exactly the same complement as in the escaping join. -/
theorem parabolic_join_mem_HOver {Y : Subgroup G}
    (hlocal : Y ∈ Chapter1.L G (T : Subgroup G))
    (hmax : Order.HasUniqueMaximalOver (T : Subgroup G) (Y ⊔ (T : Subgroup G))) :
    ((Y ⊔ (T : Subgroup G)) ⊔ A.subgroup) ∈ Chapter1.HOver G (T : Set G) := by
  have he : (Y ⊔ (T : Subgroup G)) ⊔ A.subgroup =
      normalizer (T : Set G) ⊔ (Y ⊔ (T : Subgroup G)) := by
    apply le_antisymm
    · exact sup_le le_sup_right (A.normalizes.trans le_sup_left)
    · refine sup_le ?_ le_sup_left
      rw [← A.generate]
      exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  refine ⟨?_, show (T : Subgroup G) ≤ (Y ⊔ (T : Subgroup G)) ⊔ A.subgroup from
    le_sup_right.trans le_sup_left⟩
  rw [he]
  exact parabolic_join_core_ne_bot S.source D ⟨hlocal.2.2, show (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G) from le_sup_right⟩ hmax

end OddSupplement
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
