module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.WordTests
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupNormalizers.WordActions
public import Theory.SpecificGroups.Held.Model.FourPointBase
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.FinCases

/-!
# Subgroups of order nine in two Held four-group normalizers

Two explicit commuting cubic elements normalize each of the literal rows 1
and 3. Their nine products have distinct images at vertex zero, so they give
an embedded C₃ × C₃ in the full Held normalizer. Generator conjugation and
the cubic identities are checked on Held's certified four-point base.

Sources: Aschbacher–Smith 15.3.43, printed p.1140; GLS3 Table 5.3p;
the original ATLAS HeG1-p2058B0 carrier. GAP only discovered the words;
all identities and the nine distinct images are checked in Lean's kernel.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupNormalizers
open Subgroup ProperInclusions

set_option Elab.async false

private def cubicHom {G : Type*} [Group G] (a : G) (ha : a ^ 3 = 1) :
    Multiplicative (ZMod 3) →* G where
  toFun i := a ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change a ^ (i.toAdd + j.toAdd).val = _
    rw [ZMod.val_add, ← pow_add]
    exact pow_eq_pow_of_modEq (Nat.mod_mod _ _) ha

private theorem nine_dvd_of_cubic_pair {G : Type*} [Group G] [Finite G] (a b : G)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : Commute a b)
    (hi : Function.Injective (fun ij : Fin 3 × Fin 3 => a ^ ij.1.val * b ^ ij.2.val)) :
    9 ∣ Nat.card G := by
  let f := (cubicHom a ha).noncommCoprod (cubicHom b hb)
    (fun i j => hc.pow_pow _ _)
  have hfi : Function.Injective f := by
    intro i j hij
    have he := hi (show a ^ (⟨i.1.toAdd.val, i.1.toAdd.val_lt⟩ : Fin 3).val *
        b ^ (⟨i.2.toAdd.val, i.2.toAdd.val_lt⟩ : Fin 3).val =
        a ^ (⟨j.1.toAdd.val, j.1.toAdd.val_lt⟩ : Fin 3).val *
        b ^ (⟨j.2.toAdd.val, j.2.toAdd.val_lt⟩ : Fin 3).val from hij)
    apply Prod.ext
    · exact congrArg Multiplicative.ofAdd (ZMod.val_injective 3 (congrArg (fun p => p.1.val) he))
    · exact congrArg Multiplicative.ofAdd (ZMod.val_injective 3 (congrArg (fun p => p.2.val) he))
  simpa only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3), Nat.card_zmod] using
    Subgroup.card_dvd_of_injective f hfi

private def row : Fin 2 → Fin 22
  | 0 => 1
  | _ => 3

private def cubicWord : Fin 2 → Fin 2 → List ℤ
  | 0, 0 => [1, -2, 1, -2, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, -2, 1, 2, 1, 2, 1, 2, -1, 2, 1, -2, -2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 2, 1]
  | 0, 1 => [1, 2, 1, 2, 2, 1, 2, 2, 1, -2, -2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, -1, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -2, 1, -2, 1, 2, 2, 2, 1, 2, 1, -2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, -2, 1, 2, 1, 2]
  | 1, 0 => [1, -2, 1, -2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, -1, -2, 1, 2, 1, -2, -2, -2, 1, 2, 2, 2, 1, -2, -2, -2, 1, 2, 2, 1, 2, 1, -2, -2, -2, -1, 2, -1, -2, -2, -1, 2, -1, -2, -1, -2, -2, -1, -2, -1, -2]
  | 1, 1 => [-2, -1, 2, -1, -2, -1, 2, -1, 2, 2, -1, 2, -1, -2, -1, -2, -2, -1, 2, 2, -1, -2, -1, -2, -2, -2, -1, -2, -1, 2, 2, 2, -1, 2, -1, 2, 2, 1, -2, -2, -2, -1, -2, -2, -2, -2, -1, -2, -2, -2, -2, -1, 2, 2, -1, -2, -1, -2, -1, 2, -1, -2]

private def cubic (k t : Fin 2) : He :=
  ((cubicWord k t).map (fun n =>
    if n.natAbs = 1 then a ^ n else b ^ (if n < 0 then (-1 : ℤ) else 1))).prod

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem cube_0_0 : cubic 0 0 ^ 3 = 1 := by
  apply eq_of_four_point_images
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem cube_0_1 : cubic 0 1 ^ 3 = 1 := by
  apply eq_of_four_point_images
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem cube_1_0 : cubic 1 0 ^ 3 = 1 := by
  apply eq_of_four_point_images
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem cube_1_1 : cubic 1 1 ^ 3 = 1 := by
  apply eq_of_four_point_images
  decide +kernel

private theorem cubic_cubed (k t : Fin 2) : cubic k t ^ 3 = 1 := by
  fin_cases k <;> fin_cases t
  · exact cube_0_0
  · exact cube_0_1
  · exact cube_1_0
  · exact cube_1_1

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem commute_0 : cubic 0 0 * cubic 0 1 = cubic 0 1 * cubic 0 0 := by
  apply eq_of_four_point_images
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem commute_1 : cubic 1 0 * cubic 1 1 = cubic 1 1 * cubic 1 0 := by
  apply eq_of_four_point_images
  decide +kernel

private theorem cubic_commute (k : Fin 2) : Commute (cubic k 0) (cubic k 1) := by
  fin_cases k
  · exact commute_0
  · exact commute_1

private def imageFactors : Fin 2 → Fin 2 → Fin 2 → List ℕ
  | 0, 0, 0 => [0, 1]
  | 0, 0, 1 => [0]
  | 1, 0, 0 => [1]
  | 1, 0, 1 => [0, 1]
  | _, _, 0 => [0]
  | _, _, _ => [1]

private def fastRow (k : Fin 2) (i : ℕ) : Equiv.Perm (Fin 2058) :=
  WordActions.fastWord ((generatorWords (row k))[i]?.getD [])

private theorem fastRow_eq (k : Fin 2) (i : ℕ) :
    fastRow k i = representation (rowElement (row k) i) :=
  WordActions.fastWord_eq _

private def fastProduct (k : Fin 2) (is : List ℕ) : Equiv.Perm (Fin 2058) :=
  (is.map (fastRow k)).prod

private theorem fastProduct_eq (k : Fin 2) (is : List ℕ) :
    fastProduct k is = representation (rowProduct (row k) is) := by
  unfold fastProduct rowProduct
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left (fun i _ => fastRow_eq k i)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem conjugate_0_0_0 :
    cubic 0 0 * rowElement (row 0) 0 * (cubic 0 0)⁻¹ =
      rowProduct (row 0) (imageFactors 0 0 0) := by
  apply eq_of_four_point_images
  have h : ∀ x : Fin 4,
      (representation (cubic 0 0) * fastRow 0 0 *
        (representation (cubic 0 0))⁻¹) ⟨x.val, by omega⟩ =
      fastProduct 0 (imageFactors 0 0 0) ⟨x.val, by omega⟩ := by
    decide +kernel
  simpa only [fastRow_eq, fastProduct_eq, map_mul, map_inv] using h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem conjugate_0_0_1 :
    cubic 0 0 * rowElement (row 0) 1 * (cubic 0 0)⁻¹ =
      rowProduct (row 0) (imageFactors 0 0 1) := by
  apply eq_of_four_point_images
  have h : ∀ x : Fin 4,
      (representation (cubic 0 0) * fastRow 0 1 *
        (representation (cubic 0 0))⁻¹) ⟨x.val, by omega⟩ =
      fastProduct 0 (imageFactors 0 0 1) ⟨x.val, by omega⟩ := by
    decide +kernel
  simpa only [fastRow_eq, fastProduct_eq, map_mul, map_inv] using h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem conjugate_0_1_0 :
    cubic 0 1 * rowElement (row 0) 0 * (cubic 0 1)⁻¹ =
      rowProduct (row 0) (imageFactors 0 1 0) := by
  apply eq_of_four_point_images
  have h : ∀ x : Fin 4,
      (representation (cubic 0 1) * fastRow 0 0 *
        (representation (cubic 0 1))⁻¹) ⟨x.val, by omega⟩ =
      fastProduct 0 (imageFactors 0 1 0) ⟨x.val, by omega⟩ := by
    decide +kernel
  simpa only [fastRow_eq, fastProduct_eq, map_mul, map_inv] using h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem conjugate_0_1_1 :
    cubic 0 1 * rowElement (row 0) 1 * (cubic 0 1)⁻¹ =
      rowProduct (row 0) (imageFactors 0 1 1) := by
  apply eq_of_four_point_images
  have h : ∀ x : Fin 4,
      (representation (cubic 0 1) * fastRow 0 1 *
        (representation (cubic 0 1))⁻¹) ⟨x.val, by omega⟩ =
      fastProduct 0 (imageFactors 0 1 1) ⟨x.val, by omega⟩ := by
    decide +kernel
  simpa only [fastRow_eq, fastProduct_eq, map_mul, map_inv] using h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem conjugate_1_0_0 :
    cubic 1 0 * rowElement (row 1) 0 * (cubic 1 0)⁻¹ =
      rowProduct (row 1) (imageFactors 1 0 0) := by
  apply eq_of_four_point_images
  have h : ∀ x : Fin 4,
      (representation (cubic 1 0) * fastRow 1 0 *
        (representation (cubic 1 0))⁻¹) ⟨x.val, by omega⟩ =
      fastProduct 1 (imageFactors 1 0 0) ⟨x.val, by omega⟩ := by
    decide +kernel
  simpa only [fastRow_eq, fastProduct_eq, map_mul, map_inv] using h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem conjugate_1_0_1 :
    cubic 1 0 * rowElement (row 1) 1 * (cubic 1 0)⁻¹ =
      rowProduct (row 1) (imageFactors 1 0 1) := by
  apply eq_of_four_point_images
  have h : ∀ x : Fin 4,
      (representation (cubic 1 0) * fastRow 1 1 *
        (representation (cubic 1 0))⁻¹) ⟨x.val, by omega⟩ =
      fastProduct 1 (imageFactors 1 0 1) ⟨x.val, by omega⟩ := by
    decide +kernel
  simpa only [fastRow_eq, fastProduct_eq, map_mul, map_inv] using h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem conjugate_1_1_0 :
    cubic 1 1 * rowElement (row 1) 0 * (cubic 1 1)⁻¹ =
      rowProduct (row 1) (imageFactors 1 1 0) := by
  apply eq_of_four_point_images
  have h : ∀ x : Fin 4,
      (representation (cubic 1 1) * fastRow 1 0 *
        (representation (cubic 1 1))⁻¹) ⟨x.val, by omega⟩ =
      fastProduct 1 (imageFactors 1 1 0) ⟨x.val, by omega⟩ := by
    decide +kernel
  simpa only [fastRow_eq, fastProduct_eq, map_mul, map_inv] using h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem conjugate_1_1_1 :
    cubic 1 1 * rowElement (row 1) 1 * (cubic 1 1)⁻¹ =
      rowProduct (row 1) (imageFactors 1 1 1) := by
  apply eq_of_four_point_images
  have h : ∀ x : Fin 4,
      (representation (cubic 1 1) * fastRow 1 1 *
        (representation (cubic 1 1))⁻¹) ⟨x.val, by omega⟩ =
      fastProduct 1 (imageFactors 1 1 1) ⟨x.val, by omega⟩ := by
    decide +kernel
  simpa only [fastRow_eq, fastProduct_eq, map_mul, map_inv] using h

private theorem conjugate_generator (k t i : Fin 2) :
    cubic k t * rowElement (row k) i.val * (cubic k t)⁻¹ =
      rowProduct (row k) (imageFactors k t i) := by
  fin_cases k <;> fin_cases t <;> fin_cases i
  · exact conjugate_0_0_0
  · exact conjugate_0_0_1
  · exact conjugate_0_1_0
  · exact conjugate_0_1_1
  · exact conjugate_1_0_0
  · exact conjugate_1_0_1
  · exact conjugate_1_1_0
  · exact conjugate_1_1_1

private theorem cubic_mem (k t : Fin 2) :
    cubic k t ∈ normalizer (ambient (row k) : Set He) := by
  apply mem_normalizer_of_words
  intro w hw
  have h (i : Fin 2) :
      cubic k t * rowElement (row k) i.val * (cubic k t)⁻¹ ∈ ambient (row k) := by
    rw [conjugate_generator]
    exact rowProduct_mem _ _
  have hwords : generatorWords (row k) =
      [((generatorWords (row k))[0]?.getD []), ((generatorWords (row k))[1]?.getD [])] := by
    have hall : ∀ k : Fin 2, generatorWords (row k) =
        [((generatorWords (row k))[0]?.getD []), ((generatorWords (row k))[1]?.getD [])] := by
      decide +kernel
    exact hall k
  rw [hwords, List.mem_cons, List.mem_singleton] at hw
  rcases hw with hw | hw
  · rw [hw]
    exact h 0
  · rw [hw]
    exact h 1

private def imageTable : Fin 2 → Fin 3 → Fin 3 → Fin 2058
  | 0, 0, 0 => 0
  | 0, 0, 1 => 1442
  | 0, 0, _ => 326
  | 0, 1, 0 => 1455
  | 0, 1, 1 => 897
  | 0, 1, _ => 1232
  | 0, _, 0 => 1112
  | 0, _, 1 => 1244
  | 0, _, _ => 385
  | _, 0, 0 => 0
  | _, 0, 1 => 1367
  | _, 0, _ => 481
  | _, 1, 0 => 49
  | _, 1, 1 => 1450
  | _, 1, _ => 1235
  | _, _, 0 => 355
  | _, _, 1 => 1077
  | _, _, _ => 820

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_0_0_0 :
    representation (cubic 0 0 ^ 0 * cubic 0 1 ^ 0) 0 = imageTable 0 0 0 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_0_0_1 :
    representation (cubic 0 0 ^ 0 * cubic 0 1 ^ 1) 0 = imageTable 0 0 1 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_0_0_2 :
    representation (cubic 0 0 ^ 0 * cubic 0 1 ^ 2) 0 = imageTable 0 0 2 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_0_1_0 :
    representation (cubic 0 0 ^ 1 * cubic 0 1 ^ 0) 0 = imageTable 0 1 0 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_0_1_1 :
    representation (cubic 0 0 ^ 1 * cubic 0 1 ^ 1) 0 = imageTable 0 1 1 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_0_1_2 :
    representation (cubic 0 0 ^ 1 * cubic 0 1 ^ 2) 0 = imageTable 0 1 2 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_0_2_0 :
    representation (cubic 0 0 ^ 2 * cubic 0 1 ^ 0) 0 = imageTable 0 2 0 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_0_2_1 :
    representation (cubic 0 0 ^ 2 * cubic 0 1 ^ 1) 0 = imageTable 0 2 1 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_0_2_2 :
    representation (cubic 0 0 ^ 2 * cubic 0 1 ^ 2) 0 = imageTable 0 2 2 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_1_0_0 :
    representation (cubic 1 0 ^ 0 * cubic 1 1 ^ 0) 0 = imageTable 1 0 0 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_1_0_1 :
    representation (cubic 1 0 ^ 0 * cubic 1 1 ^ 1) 0 = imageTable 1 0 1 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_1_0_2 :
    representation (cubic 1 0 ^ 0 * cubic 1 1 ^ 2) 0 = imageTable 1 0 2 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_1_1_0 :
    representation (cubic 1 0 ^ 1 * cubic 1 1 ^ 0) 0 = imageTable 1 1 0 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_1_1_1 :
    representation (cubic 1 0 ^ 1 * cubic 1 1 ^ 1) 0 = imageTable 1 1 1 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_1_1_2 :
    representation (cubic 1 0 ^ 1 * cubic 1 1 ^ 2) 0 = imageTable 1 1 2 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_1_2_0 :
    representation (cubic 1 0 ^ 2 * cubic 1 1 ^ 0) 0 = imageTable 1 2 0 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_1_2_1 :
    representation (cubic 1 0 ^ 2 * cubic 1 1 ^ 1) 0 = imageTable 1 2 1 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem image_1_2_2 :
    representation (cubic 1 0 ^ 2 * cubic 1 1 ^ 2) 0 = imageTable 1 2 2 := by
  decide +kernel

private theorem product_image (k : Fin 2) (i j : Fin 3) :
    representation (cubic k 0 ^ i.val * cubic k 1 ^ j.val) 0 = imageTable k i j := by
  fin_cases k <;> fin_cases i <;> fin_cases j
  · exact image_0_0_0
  · exact image_0_0_1
  · exact image_0_0_2
  · exact image_0_1_0
  · exact image_0_1_1
  · exact image_0_1_2
  · exact image_0_2_0
  · exact image_0_2_1
  · exact image_0_2_2
  · exact image_1_0_0
  · exact image_1_0_1
  · exact image_1_0_2
  · exact image_1_1_0
  · exact image_1_1_1
  · exact image_1_1_2
  · exact image_1_2_0
  · exact image_1_2_1
  · exact image_1_2_2

private theorem table_injective (k : Fin 2) :
    Function.Injective (fun ij : Fin 3 × Fin 3 => imageTable k ij.1 ij.2) := by
  have h : ∀ k : Fin 2,
      Function.Injective (fun ij : Fin 3 × Fin 3 => imageTable k ij.1 ij.2) := by
    decide +kernel
  exact h k

private theorem nine_dvd_row (k : Fin 2) :
    9 ∣ Nat.card (normalizer (ambient (row k) : Set He)) := by
  let x : normalizer (ambient (row k) : Set He) := ⟨cubic k 0, cubic_mem k 0⟩
  let y : normalizer (ambient (row k) : Set He) := ⟨cubic k 1, cubic_mem k 1⟩
  apply nine_dvd_of_cubic_pair x y
  · exact Subtype.ext (cubic_cubed k 0)
  · exact Subtype.ext (cubic_cubed k 1)
  · exact Subtype.ext (cubic_commute k).eq
  · intro i j hij
    apply table_injective k
    have he := congrArg (fun g : normalizer (ambient (row k) : Set He) =>
      representation g.val 0) hij
    exact (product_image k i.1 i.2).symm.trans (he.trans (product_image k j.1 j.2))

/-- The first literal four-group has full normalizer order divisible by nine. -/
public theorem nine_dvd_normalizer_one :
    9 ∣ Nat.card (normalizer (ambient 1 : Set He)) := nine_dvd_row 0

/-- The third literal four-group has full normalizer order divisible by nine. -/
public theorem nine_dvd_normalizer_three :
    9 ∣ Nat.card (normalizer (ambient 3 : Set He)) := nine_dvd_row 1

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupNormalizers
