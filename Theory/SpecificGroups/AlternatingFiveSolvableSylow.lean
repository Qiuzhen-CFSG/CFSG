module

public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.Five
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.GroupTheory.SylowInnerAction
public import Mathlib.GroupTheory.IsPerfect

/-!
# Solvable Sylow overgroups in A₅

A proper subgroup of A₅ containing a Sylow four-group has order at most
twelve, divisible by four, and dividing sixty. Thus its order is coprime
to five. The permutation calculation in `SylowFixedQuotients.Five` makes
it normalize that four-group. This applies in particular to solvable
overgroups, since A₅ is perfect and nontrivial.

The final action calculation combines this normality with Sylow
maximality for inner conjugators and coprimality of the odd subgroup.

Source: Aschbacher–Smith, proof of Lemma 1.3.9(1), printed p.514;
the actual A₅ subgroup calculation used in its swapped-component case.
-/

open Subgroup
open Theory.PSL2.SylowFixedQuotients
namespace alternatingGroup
local notation "A5" => alternatingGroup (Fin 5)

private theorem card_five : Nat.card A5 = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem proper_card_le (J : Subgroup A5) (hJ : J ≠ ⊤) : Nat.card J ≤ 12 := by
  let : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  have hi : 5 ≤ J.index := by
    by_contra hn
    apply hJ
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    have hb := Nat.factorial_le (show J.index ≤ 4 by omega)
    rw [card_five]
    norm_num [Nat.factorial] at hb ⊢
    omega
  have hp := J.card_mul_index
  rw [card_five] at hp
  nlinarith

/-- A proper overgroup of a Sylow four-group of A₅ normalizes it. -/
public theorem proper_sylow_overgroup_le_normalizer (S : Sylow 2 A5)
    (J : Subgroup A5) (hJ : J ≠ ⊤) (hSJ : (S : Subgroup A5) ≤ J) :
    J ≤ normalizer (S : Set A5) := by
  have hfour : 4 ∣ Nat.card J := by
    rw [← alternating_sylow_card S]
    exact card_dvd_of_le hSJ
  have hd : Nat.card J ∣ 60 := card_five ▸ J.card_subgroup_dvd_card
  have hb := proper_card_le J hJ
  have hc : (Nat.card J).Coprime 5 := by
    generalize Nat.card J = n at *
    interval_cases n <;> first | omega | decide
  apply alternating_mutual_normalizes_of_no_five S J
  · intro x hx hpow
    have he : (⟨x, hx⟩ : J) = 1 := (powCoprime hc).injective (by
      change (⟨x, hx⟩ : J) ^ 5 = 1 ^ 5
      simp only [one_pow]
      exact Subtype.ext hpow)
    exact congrArg Subtype.val he
  · exact hSJ.trans J.le_normalizer

/-- A solvable overgroup of a Sylow four-group of A₅ normalizes it. -/
public theorem solvable_sylow_overgroup_le_normalizer (S : Sylow 2 A5)
    (J : Subgroup A5) [Group.IsSolvable J] (hSJ : (S : Subgroup A5) ≤ J) :
    J ≤ normalizer (S : Set A5) := by
  apply proper_sylow_overgroup_le_normalizer S J _ hSJ
  intro ht
  have : Group.IsPerfect A5 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have : Group.IsSolvable A5 := Group.isSolvable_of_surjective
    (f := J.subtype) (by rw [ht]; exact topEquiv.surjective)
  exact Group.IsPerfect.not_isSolvable A5 inferInstance

variable {G : Type*} [Group G] [Finite G]

/-- Transport the normalizer assertion through an actual A₅ isomorphism. -/
public theorem solvable_sylow_overgroup_le_normalizer_of_equiv
    (e : G ≃* alternatingGroup (Fin 5)) (S : Sylow 2 G)
    (J : Subgroup G) [Group.IsSolvable J] (hSJ : (S : Subgroup G) ≤ J) :
    J ≤ normalizer (S : Set G) := by
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let I := J.map e.toMonoidHom
  have : Group.IsSolvable I := Group.isSolvable_of_surjective
    (e.toMonoidHom.subgroupMap_surjective J)
  have he := solvable_sylow_overgroup_le_normalizer Q I (map_mono hSJ)
  change J.map e.toMonoidHom ≤
    normalizer ((S : Subgroup G).map e.toMonoidHom : Set _) at he
  rw [← Subgroup.map_equiv_normalizer_eq] at he
  exact (Subgroup.map_le_map_iff_of_injective e.injective).mp he

end alternatingGroup
