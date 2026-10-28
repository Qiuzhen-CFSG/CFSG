module
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralWord
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup.Tables
public import Theory.GroupTheory.BinaryCollection
/-!
# Words and binary products for the two Held rank-four rows

The two rows are the unchanged catalogue entries 9 and 11. Their permutation
words reuse the already checked four representative-generator tables. The map
identities below identify every table expression with the actual Held element;
no subgroup cardinality or exhaustiveness is asserted by these definitions.

Source: ATLAS HeG1-p2058B0 and the catalogue discovery data; GLS3 Table 5.3p.
-/

public section
open Subgroup MulAction
namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankFourKernel
open LocalPairs.SylowGeometry.Calculations
open LocalPairs.SylowGeometry.Calculations.TwoGroup.Tables
@[expose] public def tableGen : Fin 4 → Equiv.Perm (Fin 2058)
 | 0 => g0
 | 1 => g1
 | 2 => g2
 | 3 => g3
@[expose] public def tableWord (w : List ℤ) : Equiv.Perm (Fin 2058) :=
 (w.map (fun k => if k < 0 then (tableGen (Fin.ofNat 4 (k.natAbs - 1)))⁻¹
   else tableGen (Fin.ofNat 4 (k.natAbs - 1)))).prod
@[expose] public def row (k : Fin 2) : Fin 22 := if k = 0 then 9 else 11
@[expose] public def genWord (k : Fin 2) (i : Fin 4) : List ℤ :=
 ((generatorWords (row k))[i.val]?).getD []
@[expose] public def gen (k : Fin 2) (i : Fin 4) : He := word (genWord k i)
@[expose] public def perm (k : Fin 2) (i : Fin 4) : Equiv.Perm (Fin 2058) :=
 tableWord (genWord k i)

theorem tableGen_eq (i : Fin 4) : tableGen i = representation (generator i) := by
  fin_cases i
  · exact g0_eq
  · exact g1_eq
  · exact g2_eq
  · exact g3_eq

theorem tableWord_eq (w : List ℤ) : tableWord w = representation (word w : He) := by
  change tableWord w = (representation.comp representative.subtype) (word w)
  simp only [tableWord, word, map_list_prod, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro n _
  simp only [letter]
  split_ifs <;> simp only [map_inv, MonoidHom.coe_comp, Function.comp_apply,
    tableGen_eq] <;> rfl

theorem perm_eq (k : Fin 2) (i : Fin 4) : perm k i = representation (gen k i) :=
  tableWord_eq _

theorem words_row (k : Fin 2) : generatorWords (row k) = List.ofFn (genWord k) := by
  have h : ∀ k : Fin 2, generatorWords (row k) = List.ofFn (genWord k) := by decide +kernel
  exact h k

theorem ambient_eq_closure (k : Fin 2) :
    ambient (row k) = closure (Set.range (gen k)) := by
  rw [ambient, entry, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    rw [words_row] at hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨word (genWord k i), ⟨genWord k i, by
      rw [words_row]; exact List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩, rfl⟩

theorem gen_mem (k : Fin 2) (i : Fin 4) : gen k i ∈ ambient (row k) := by
  rw [ambient_eq_closure]
  exact subset_closure (Set.mem_range_self i)

theorem gen_three (k : Fin 2) : gen k 3 = centralWord := by
  fin_cases k <;> rfl

@[expose] public def normalForm (k : Fin 2) (n : Fin 16) : He :=
  Theory.GroupTheory.BinaryCollection.product (List.ofFn (gen k)) n.val
@[expose] public def permForm (k : Fin 2) (n : Fin 16) : Equiv.Perm (Fin 2058) :=
  Theory.GroupTheory.BinaryCollection.product (List.ofFn (perm k)) n.val

private theorem map_product {G H : Type*} [Group G] [Group H]
    (f : G →* H) (l : List G) (n : ℕ) :
    f (Theory.GroupTheory.BinaryCollection.product l n) =
      Theory.GroupTheory.BinaryCollection.product (l.map f) n := by
  induction l generalizing n with
  | nil => exact f.map_one
  | cons a l ih => simp only [Theory.GroupTheory.BinaryCollection.product,
      List.map_cons, map_mul, map_pow, ih]

theorem permForm_eq (k : Fin 2) (n : Fin 16) :
    permForm k n = representation (normalForm k n) := by
  rw [normalForm, map_product, List.map_ofFn]
  change _ = Theory.GroupTheory.BinaryCollection.product
    (List.ofFn (fun i => representation (gen k i))) n.val
  simp only [← perm_eq]
  rfl

theorem normalForm_zero (k : Fin 2) : normalForm k 0 = 1 := by
  simp [normalForm, Theory.GroupTheory.BinaryCollection.product, List.ofFn_succ]

theorem normalForm_eight (k : Fin 2) : normalForm k 8 = centralWord := by
  simpa [normalForm, Theory.GroupTheory.BinaryCollection.product, List.ofFn_succ] using gen_three k

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankFourKernel
