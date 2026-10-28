module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.LiteralLocal.Action
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Planes

/-!
# Cubic action certificates on the literal Held seed

Conjugating the first published order-nine plane by the cube of the second
max3 generator gives two elements normalizing the unchanged join of catalogue
rows 20 and 21. We check the conjugates of all twelve seed generators on the
faithful four-point base. For each of the eight nonzero plane coordinates,
thirteen commutators have distinct images of vertex zero, giving the strict
cardinality bound without enumerating the normalizer or the commutator group.

The GAP discovery data are retained in `source/`; all identities and distinctness
claims below are checked by the Lean kernel. Source: ATLAS HeG1-p2058B0;
GLS3 Table 5.3p (including its fused-classes convention); Aschbacher--Smith,
Lemma 2.3.9(7), printed p.526. This is a calculation for the literal seed,
not for either elementary order-64 subgroup separately.
-/

public section

namespace Held.AutomorphismLocalPair.CubicCommutators
open scoped commutatorElement
open Subgroup LiteralLocal LocalPairs.PairCoverage LocalPairs.PairCoverage.LocalActions
open LocalPairs.PairCoverage.LocalActions.RepresentativeImages

@[expose] def conjugator : He := localWord false ^ 3

@[expose] def gen (k : Fin 2) : He := (MulAut.conj conjugator) (oddGenerator false 0 k)

private def perm (k : Fin 2) : Equiv.Perm (Fin 2058) :=
  Local0.localPerm ^ 3 * (if k = 0 then Pair00.odd0 else Pair00.odd1) *
    (Local0.localPerm ^ 3)⁻¹

private theorem perm_eq (k : Fin 2) : perm k = representation (gen k) := by
  change _ = representation (conjugator * oddGenerator false 0 k * conjugator⁻¹)
  simp only [map_mul, map_inv, conjugator, map_pow, ← Local0.localPerm_eq]
  fin_cases k
  · change Local0.localPerm ^ 3 * Pair00.odd0 * (Local0.localPerm ^ 3)⁻¹ = _
    rw [Pair00.odd0_eq]
    rfl
  · change Local0.localPerm ^ 3 * Pair00.odd1 * (Local0.localPerm ^ 3)⁻¹ = _
    rw [Pair00.odd1_eq]
    rfl

attribute [local irreducible] gen conjugator

private def conjugateWord : Fin 2 → Fin 12 → List (Fin 12)
  | 0, 0 => [0, 1, 4, 5]
  | 0, 1 => [1, 2]
  | 0, 2 => [1, 2, 3, 4]
  | 0, 3 => [1, 4, 5]
  | 0, 4 => [4, 5]
  | 0, 5 => [2, 3]
  | 0, 6 => [9]
  | 0, 7 => [10]
  | 0, 8 => [5, 6, 8]
  | 0, 9 => [6, 9]
  | 0, 10 => [7, 10]
  | 0, 11 => [2, 3]
  | 1, 0 => [6, 4, 6]
  | 1, 1 => [0, 1, 5]
  | 1, 2 => [1, 3, 4]
  | 1, 3 => [2, 3]
  | 1, 4 => [0, 4, 5]
  | 1, 5 => [2, 6, 7]
  | 1, 6 => [5, 10]
  | 1, 7 => [10]
  | 1, 8 => [5, 6, 10]
  | 1, 9 => [2, 7, 9]
  | 1, 10 => [7, 10]
  | 1, 11 => [2, 6, 7]

set_option maxRecDepth 16384 in
private theorem conjugate_check : ∀ k : Fin 2, ∀ i : Fin 12, ∀ v : Fin 4,
    (perm k * seedPerm i * (perm k)⁻¹) ⟨v.val, by omega⟩ =
      seedPermWord (conjugateWord k i) ⟨v.val, by omega⟩ := by
  decide +kernel

theorem gen_mem_normalizer (k : Fin 2) : gen k ∈ representativeLargeLocal := by
  have hle : representativeLargeSeed ≤
      representativeLargeSeed.comap (MulAut.conj (gen k)).toMonoidHom := by
    apply seed_le_of_generators
    intro i
    change gen k * seedGen i * (gen k)⁻¹ ∈ representativeLargeSeed
    have he : gen k * seedGen i * (gen k)⁻¹ = seedWord (conjugateWord k i) := by
      apply eq_of_four_point_images
      simp only [map_mul, map_inv, ← perm_eq, ← seedPerm_eq, ← seedPermWord_eq]
      exact conjugate_check k i
    rw [he]
    exact seedWord_mem _
  have hm : representativeLargeSeed.map (MulAut.conj (gen k)).toMonoidHom ≤
      representativeLargeSeed := map_le_iff_le_comap.mpr hle
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact eq_of_le_of_card_ge hm (by
    rw [card_map_of_injective (MulAut.conj (gen k)).injective])

@[expose] def first (k : Fin 8) : Fin 3 := ⟨(k.val + 1) / 3, by omega⟩
@[expose] def second (k : Fin 8) : Fin 3 := ⟨(k.val + 1) % 3, Nat.mod_lt _ (by decide)⟩

@[expose] def element (k : Fin 8) : He := gen 0 ^ (first k).val * gen 1 ^ (second k).val

private def elementPerm (k : Fin 8) : Equiv.Perm (Fin 2058) :=
  perm 0 ^ (first k).val * perm 1 ^ (second k).val

private theorem elementPerm_eq (k : Fin 8) : elementPerm k = representation (element k) := by
  simp only [elementPerm, element, map_mul, map_pow, perm_eq]

private def witnessWord : Fin 8 → Fin 13 → List (Fin 12)
  | 0 => ![[], [0], [1], [2], [3], [6], [7], [8], [9], [10], [0, 1], [0, 2], [0, 3]]
  | 1 => ![[], [0], [1], [2], [3], [6], [7], [8], [9], [10], [0, 1], [0, 2], [0, 3]]
  | 2 => ![[], [0], [1], [2], [3], [4], [5], [6], [7], [8], [9], [10], [0, 1]]
  | 3 => ![[], [0], [1], [3], [4], [5], [6], [7], [8], [9], [0, 1], [0, 3], [0, 4]]
  | 4 => ![[], [1], [2], [3], [4], [6], [1, 2], [1, 4], [2, 3], [2, 4], [2, 6], [3, 4], [4, 6]]
  | 5 => ![[], [0], [1], [2], [3], [4], [5], [6], [7], [8], [9], [10], [0, 1]]
  | 6 => ![[], [1], [2], [3], [4], [6], [1, 2], [1, 4], [2, 3], [2, 4], [2, 6], [3, 4], [4, 6]]
  | 7 => ![[], [0], [1], [3], [4], [5], [6], [7], [8], [9], [0, 1], [0, 3], [0, 4]]

private def images : Fin 8 → Fin 13 → Fin 2058
  | 0 => ![0, 374, 1395, 49, 355, 1846, 1994, 1077, 450, 1419, 219, 125, 581]
  | 1 => ![0, 1455, 125, 1631, 49, 334, 1640, 1846, 1054, 1994, 1796, 1514, 1044]
  | 2 => ![0, 1514, 355, 1631, 1796, 1395, 219, 417, 1994, 617, 1715, 1419, 1044]
  | 3 => ![0, 1395, 1796, 919, 49, 1044, 371, 1640, 1994, 1157, 1631, 355, 66]
  | 4 => ![0, 374, 49, 1395, 1455, 219, 125, 919, 66, 1044, 1514, 581, 355]
  | 5 => ![0, 581, 1631, 49, 1514, 219, 374, 732, 1640, 1054, 417, 1994, 125]
  | 6 => ![0, 66, 1631, 1455, 581, 1112, 919, 1044, 1514, 125, 374, 1395, 49]
  | 7 => ![0, 66, 1112, 1044, 1395, 125, 1150, 1994, 1419, 1093, 1455, 581, 49]

set_option maxRecDepth 16384 in
private theorem images_check : ∀ k : Fin 8, ∀ j : Fin 13,
    ⁅seedPermWord (witnessWord k j), elementPerm k⁆ (0 : Fin 2058) = images k j := by
  decide +kernel

private theorem images_injective : ∀ k : Fin 8, Function.Injective (images k) := by
  decide +kernel

private theorem commutator_image (k : Fin 8) (j : Fin 13) :
    representation (⁅seedWord (witnessWord k j), element k⁆) 0 = images k j := by
  rw [map_commutatorElement, ← seedPermWord_eq, ← elementPerm_eq]
  exact images_check k j

theorem element_commutator_bound (k : Fin 8) :
    12 < Nat.card (⁅representativeLargeSeed, zpowers (element k)⁆ : Subgroup He) := by
  let f : Fin 13 → (⁅representativeLargeSeed, zpowers (element k)⁆ : Subgroup He) :=
    fun j => ⟨⁅seedWord (witnessWord k j), element k⁆,
      commutator_mem_commutator (seedWord_mem _) (mem_zpowers _)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply images_injective k
    rw [← commutator_image k i, ← commutator_image k j]
    exact congrArg (fun y : (⁅representativeLargeSeed, zpowers (element k)⁆ :
      Subgroup He) => representation (y : He) 0) hij
  exact lt_of_lt_of_le (by simp : 12 < Nat.card (Fin 13))
    (Nat.card_le_card_of_injective f hf)


end Held.AutomorphismLocalPair.CubicCommutators
