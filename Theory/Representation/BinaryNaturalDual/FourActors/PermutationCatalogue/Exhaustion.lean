module

public import Theory.Representation.BinaryNaturalDual.FourActors.Model
public import Theory.Representation.BinaryNaturalDual.FourActors.PermutationCatalogue.Representatives
public import Theory.Representation.BinaryNaturalDual.FourActors.PermutationCatalogue.Exhaustion.Tables

/-!
# Exhaustion of the elementary sixteen-subgroups in the eight-point model

Every elementary sixteen-subgroup of S₈ is conjugate into the binary-tree
Sylow subgroup. No involution interchanging its four-point blocks can occur:
its square-one centralizer has only twelve elements. In the block-preserving
base, commutation determines a common Klein subgroup on each block. The four
possible products have the three marked conjugacy types, and equality follows
from their common order sixteen.

This constructs an actual conjugating permutation. Transport through the
specified equivalence `permutationEquiv` gives subgroup-map equality in the
original automorphism group. The already proved pairwise nonconjugacy gives
uniqueness of the marked index. No classification of subgroups is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.3(3),
printed pp.391–392, PDF pp.402–403. The Thompson identification of A₀ and the
other clauses of H.9.3 belong to their separate assembly owners.
-/

public section

open Equiv Subgroup
open scoped IsMulCommutative
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals

namespace BinaryNaturalDual.FourActors.PermutationCatalogue
namespace Exhaustion

private theorem card_le_words (E : Subgroup S) (T : Finset (Fin 128))
    (h : ∀ g ∈ E, ∃ i ∈ T, treeWord i = g) : Nat.card E ≤ T.card := by
  classical
  have h' (g : E) : ∃ i : T, treeWord i.val = g.val := by
    obtain ⟨i, hi, he⟩ := h g g.property
    exact ⟨⟨i, hi⟩, he⟩
  choose f hf using h'
  have hinj : Function.Injective f := by
    intro g k he
    apply Subtype.ext
    rw [← hf g, ← hf k, he]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    Nat.card_le_card_of_injective f hinj

private theorem commute_words (E : Subgroup S) [IsElementaryAbelian 2 E]
    {i j : Fin 128} (hi : treeWord i ∈ E) (hj : treeWord j ∈ E) :
    treeWord i * treeWord j = treeWord j * treeWord i :=
  congrArg Subtype.val (mul_comm (⟨treeWord i, hi⟩ : E) ⟨treeWord j, hj⟩)

/-- An elementary subgroup of order sixteen in the tree Sylow preserves both
four-point blocks: an involution swapping them has too small a centralizer. -/
theorem index_lt_of_elementary_sixteen (E : Subgroup S) [IsElementaryAbelian 2 E]
    (hE : E ≤ treeGroup) (hcard : Nat.card E = 16)
    {i : Fin 128} (hi : treeWord i ∈ E) : i.val < 64 := by
  by_contra h
  have hi2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (treeWord i) hi
  have hbound := outer_centralizer_bound i (by omega) hi2
  have hle : Nat.card E ≤ (involutionCentralizer i).card := by
    apply card_le_words
    intro g hg
    obtain ⟨j, rfl⟩ := (mem_treeGroup g).mp (hE hg)
    refine ⟨j, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (treeWord j) hg,
      commute_words E hi hg⟩
  omega

/-- Each elementary sixteen-subgroup in the tree Sylow makes one common Klein
choice on each four-point block. The choices hold for every subgroup element. -/
theorem exists_compatible (E : Subgroup S) [IsElementaryAbelian 2 E]
    (hE : E ≤ treeGroup) (hcard : Nat.card E = 16) :
    ∃ l r : Bool, ∀ i : Fin 128, treeWord i ∈ E → compatible l r i := by
  classical
  have hbase {i : Fin 128} (hi : treeWord i ∈ E) : i.val < 64 :=
    index_lt_of_elementary_sixteen E hE hcard hi
  have hl : ∃ l : Bool, ∀ i : Fin 128, treeWord i ∈ E →
      (if l then i.val % 2 = i.val / 2 % 2 else i.val / 16 % 2 = 0) := by
    by_cases h : ∃ i : Fin 128, treeWord i ∈ E ∧ i.val / 16 % 2 = 1
    · obtain ⟨i, hi, hbit⟩ := h
      refine ⟨true, ?_⟩
      intro j hj
      exact left_control i j (hbase hi) (hbase hj)
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) (treeWord i) hi)
        hbit (commute_words E hi hj)
    · refine ⟨false, ?_⟩
      intro i hi
      have hn : i.val / 16 % 2 ≠ 1 := fun hh => h ⟨i, hi, hh⟩
      dsimp
      omega
  have hr : ∃ r : Bool, ∀ i : Fin 128, treeWord i ∈ E →
      (if r then i.val / 4 % 2 = i.val / 8 % 2 else i.val / 32 % 2 = 0) := by
    by_cases h : ∃ i : Fin 128, treeWord i ∈ E ∧ i.val / 32 % 2 = 1
    · obtain ⟨i, hi, hbit⟩ := h
      refine ⟨true, ?_⟩
      intro j hj
      exact right_control i j (hbase hi) (hbase hj)
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) (treeWord i) hi)
        hbit (commute_words E hi hj)
    · refine ⟨false, ?_⟩
      intro i hi
      have hn : i.val / 32 % 2 ≠ 1 := fun hh => h ⟨i, hi, hh⟩
      dsimp
      omega
  obtain ⟨l, hl⟩ := hl
  obtain ⟨r, hr⟩ := hr
  exact ⟨l, r, fun i hi => ⟨hl i hi, hr i hi⟩⟩

/-- The complete exhaustion inside one specified Sylow subgroup, including the
actual conjugating permutation and equality with a marked representative. -/
theorem tree_exhaustion (E : Subgroup S) [IsElementaryAbelian 2 E]
    (hE : E ≤ treeGroup) (hcard : Nat.card E = 16) :
    ∃ i : Fin 3, ∃ g : S, E.map (MulAut.conj g).toMonoidHom = permutationActor i := by
  obtain ⟨l, r, hcompat⟩ := exists_compatible E hE hcard
  refine ⟨classIndex l r, blockConjugator l r, ?_⟩
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨j, rfl⟩ := (mem_treeGroup g).mp (hE hg)
    obtain ⟨v, hv⟩ := compatible_conjugate l r j
      (index_lt_of_elementary_sixteen E hE hcard hg) (hcompat j hg)
    rw [← wordHom_range]
    exact ⟨v, hv⟩
  · have hmap : Nat.card (E.map (MulAut.conj (blockConjugator l r)).toMonoidHom) =
        Nat.card E :=
      (Nat.card_congr ((MulAut.conj (blockConjugator l r)).subgroupMap E).toEquiv).symm
    rw [permutationActor_card, hmap, hcard]

private noncomputable def treeSylow : Sylow 2 S := Sylow.ofCard treeGroup (by
  rw [card_treeGroup, card_s8]
  rw [show 40320 = 2 ^ 7 * 315 by rfl, Nat.factorization_mul (by decide) (by decide),
    Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)])

end Exhaustion

/-- Every elementary sixteen-subgroup of the actual eight-point symmetric group
is conjugate to one of the three marked permutation subgroups. -/
theorem permutationActor_exhaustive (E : Subgroup S) [IsElementaryAbelian 2 E]
    (hcard : Nat.card E = 16) :
    ∃ i : Fin 3, ∃ g : S, E.map (MulAut.conj g).toMonoidHom = permutationActor i := by
  obtain ⟨P, hP⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq S P Exhaustion.treeSylow
  have hb' := congrArg (fun Q : Sylow 2 S => (Q : Subgroup S)) hb
  change (P : Subgroup S).map (MulAut.conj b).toMonoidHom = treeGroup at hb'
  have hE : E.map (MulAut.conj b).toMonoidHom ≤ treeGroup := by
    rw [← hb']
    exact Subgroup.map_mono hP
  let : IsElementaryAbelian 2 (E.map (MulAut.conj b).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hc : Nat.card (E.map (MulAut.conj b).toMonoidHom) = 16 :=
    (Nat.card_congr ((MulAut.conj b).subgroupMap E).toEquiv).symm.trans hcard
  obtain ⟨i, c, hi⟩ := Exhaustion.tree_exhaustion _ hE hc
  refine ⟨i, c * b, ?_⟩
  rw [Subgroup.map_map] at hi
  convert hi using 2
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- Exhaustion for the actual automorphism group, transported through its
specified eight-point equivalence. The conclusion is subgroup-map equality. -/
theorem actor_exhaustive (E : Subgroup M) [IsElementaryAbelian 2 E]
    (hcard : Nat.card E = 16) :
    ∃ i : Fin 3, ∃ a : M, E.map (MulAut.conj a).toMonoidHom = actor i := by
  let : IsElementaryAbelian 2 (E.map permutationEquiv.toMonoidHom) :=
    IsElementaryAbelian.map _
  have hc : Nat.card (E.map permutationEquiv.toMonoidHom) = 16 :=
    (Nat.card_congr (permutationEquiv.subgroupMap E).toEquiv).symm.trans hcard
  obtain ⟨i, g, hi⟩ := permutationActor_exhaustive _ hc
  refine ⟨i, permutationEquiv.symm g, ?_⟩
  apply Subgroup.map_injective (f := permutationEquiv.toMonoidHom) permutationEquiv.injective
  rw [permutation_map_conj, actor_map]
  simpa using hi

/-- The marked conjugacy class index of an elementary sixteen-subgroup is unique. -/
theorem existsUnique_actor_conjugate (E : Subgroup M) [IsElementaryAbelian 2 E]
    (hcard : Nat.card E = 16) :
    ∃! i : Fin 3, ∃ a : M, E.map (MulAut.conj a).toMonoidHom = actor i := by
  obtain ⟨i, a, ha⟩ := actor_exhaustive E hcard
  refine ⟨i, ⟨a, ha⟩, ?_⟩
  rintro j ⟨b, hb⟩
  apply actor_conjugacy_injective j i (a * b⁻¹)
  rw [← hb, Subgroup.map_map]
  have hc : (MulAut.conj (a * b⁻¹)).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj a).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hc]
  exact ha

end BinaryNaturalDual.FourActors.PermutationCatalogue
