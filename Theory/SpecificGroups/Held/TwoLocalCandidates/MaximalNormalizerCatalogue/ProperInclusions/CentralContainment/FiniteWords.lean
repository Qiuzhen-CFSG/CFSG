module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.Signature
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup.Tables
import Mathlib.Tactic.FinCases

/-!
# Finite word certificates for the eight central Held containments

Binary products of the literal row generators are candidates for a row cover.
Right transitions and generator squares certify that they cover the actual
closure. The already checked generator tables compute these products in the
faithful action, with four-point tests for group equality and full fixed-point
counts for signatures. No independence or exhaustive ambient enumeration is
required. `signature_package` assembles these finite mathematical obligations.

Source: the unchanged catalogue word table, ATLAS HeG1-p2058B0 and max3W1;
GLS3 Table 5.3p, Aschbacher–Smith condition E, printed pp.3–4 and 481–482.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment
open LocalPairs.SylowGeometry.Calculations
open ProperInclusions

@[expose] public def row : Fin 8 → Fin 22
  | 0 => 2 | 1 => 4 | 2 => 6 | 3 => 7 | 4 => 13 | 5 => 14 | 6 => 15 | _ => 17

@[expose] public def dim : Fin 8 → ℕ
  | 0 => 2 | 1 => 3 | 2 => 3 | 3 => 3 | _ => 4

@[expose] public def bad : Fin 8 → ℕ
  | 1 => 6 | 3 => 6 | _ => 10

@[expose] public def bits (d n : ℕ) : List ℕ :=
  (List.range d).filter (fun r => n / 2 ^ r % 2 = 1)

@[expose] public def normalForm (k : Fin 8) (i : Fin (2 ^ dim k)) : He :=
  rowProduct (row k) (bits (dim k) i.val)

public theorem normalForm_mem (k : Fin 8) (i : Fin (2 ^ dim k)) :
    normalForm k i ∈ ambient (row k) := rowProduct_mem _ _

@[expose] public def generatorTable : Fin 4 → Equiv.Perm (Fin 2058)
  | 0 => TwoGroup.Tables.g0 | 1 => TwoGroup.Tables.g1
  | 2 => TwoGroup.Tables.g2 | _ => TwoGroup.Tables.g3

public theorem generatorTable_eq (i : Fin 4) : generatorTable i = representation (generator i) := by
  fin_cases i
  · exact TwoGroup.Tables.g0_eq
  · exact TwoGroup.Tables.g1_eq
  · exact TwoGroup.Tables.g2_eq
  · exact TwoGroup.Tables.g3_eq

@[expose] public def letterTable (k : ℤ) : Equiv.Perm (Fin 2058) :=
  let g := generatorTable (Fin.ofNat 4 (k.natAbs - 1))
  if k < 0 then g⁻¹ else g

public theorem letterTable_eq (k : ℤ) : letterTable k = representation (letter k : He) := by
  unfold letterTable letter
  split <;> simp only [generatorTable_eq]
  rfl

@[expose] public def wordTable (w : List ℤ) : Equiv.Perm (Fin 2058) :=
  (w.map letterTable).prod

public theorem wordTable_eq (w : List ℤ) : wordTable w = representation (word w : He) := by
  simp only [wordTable, word, ← Subgroup.subtype_apply, map_list_prod, List.map_map,
    Function.comp_def]
  congr 1
  exact List.map_congr_left (fun k _ => letterTable_eq k)

@[expose] public def rowTable (j : Fin 22) (i : ℕ) : Equiv.Perm (Fin 2058) :=
  wordTable ((generatorWords j)[i]?.getD [])

public theorem rowTable_eq (j : Fin 22) (i : ℕ) :
    rowTable j i = representation (rowElement j i) := wordTable_eq _

@[expose] public def normalTable (k : Fin 8) (i : Fin (2 ^ dim k)) : Equiv.Perm (Fin 2058) :=
  ((bits (dim k) i.val).map (rowTable (row k))).prod

public theorem normalTable_eq (k : Fin 8) (i : Fin (2 ^ dim k)) :
    normalTable k i = representation (normalForm k i) := by
  simp only [normalTable, normalForm, rowProduct, map_list_prod, List.map_map,
    Function.comp_def]
  congr 1
  exact List.map_congr_left (fun i _ => rowTable_eq _ i)

@[expose] public def tableCommonCount (x y : Equiv.Perm (Fin 2058)) : ℕ :=
  ((List.finRange 2058).filter (fun v => x v = v ∧ y v = v)).length

public theorem tableCommonCount_eq (x y : Equiv.Perm (Fin 2058)) :
    tableCommonCount x y =
      (Finset.univ.filter (fun v : Fin 2058 => x v = v ∧ y v = v)).card := by
  rw [tableCommonCount, ← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _),
    List.toFinset_filter, List.toFinset_finRange]
  simp only [decide_eq_true_eq]

public theorem normal_count_eq (k : Fin 8) (i j : Fin (2 ^ dim k)) :
    commonFixedCount (normalForm k i) (normalForm k j) =
      tableCommonCount (normalTable k i) (normalTable k j) := by
  rw [tableCommonCount_eq, normalTable_eq, normalTable_eq]
  rfl

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment
open ProperInclusions

@[expose] public def centralIndex (k : Fin 8) : Fin (2 ^ dim k) :=
  ⟨2 ^ (dim k - 1), by fin_cases k <;> decide⟩

public theorem normalForm_central (k : Fin 8) :
    normalForm k (centralIndex k) = centralWord := by
  have hb : bits (dim k) (centralIndex k).val = [dim k - 1] := by
    fin_cases k <;> rfl
  have hw : rowElement (row k) (dim k - 1) = centralWord := by
    fin_cases k <;> rfl
  simp only [normalForm, hb, rowProduct, List.map_singleton, List.prod_singleton, hw]

public theorem centralWord_mem (k : Fin 8) : centralWord ∈ ambient (row k) := by
  rw [← normalForm_central k]
  exact normalForm_mem _ _

public theorem normalForm_zero (k : Fin 8) :
    normalForm k ⟨0, by have := dim k; positivity⟩ = 1 := by
  fin_cases k <;> rfl

@[expose] public def flipIndex (k : Fin 8) (i : Fin (2 ^ dim k)) (r : Fin (dim k)) :
    Fin (2 ^ dim k) :=
  ⟨(i.val ^^^ 2 ^ r.val) % 2 ^ dim k, Nat.mod_lt _ (by positivity)⟩

public theorem rowWord_index (k : Fin 8) (w : List ℤ) (hw : w ∈ generatorWords (row k)) :
    ∃ r : Fin (dim k), rowElement (row k) r.val = (word w : He) := by
  have hlen : (generatorWords (row k)).length = dim k := by
    fin_cases k <;> rfl
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
  obtain ⟨hb, he⟩ := List.getElem?_eq_some_iff.mp hi
  refine ⟨⟨i, hlen ▸ hb⟩, ?_⟩
  simp only [rowElement, hi, Option.getD_some]

/-- Generator involutions and right transitions cover each literal row. -/
public theorem cover_of_transitions (k : Fin 8)
    (hsq : ∀ r : Fin (dim k), rowElement (row k) r.val * rowElement (row k) r.val = 1)
    (hstep : ∀ i r, normalForm k i * rowElement (row k) r.val =
      normalForm k (flipIndex k i r)) :
    ∀ x ∈ ambient (row k), ∃ i, normalForm k i = x := by
  apply ambient_covered (normalForm k)
  · exact ⟨_, normalForm_zero k⟩
  · intro w hw i
    obtain ⟨r, hr⟩ := rowWord_index k w hw
    exact ⟨flipIndex k i r, hr ▸ hstep i r⟩
  · intro w hw i
    obtain ⟨r, hr⟩ := rowWord_index k w hw
    have hi : (word w : He)⁻¹ = word w := by
      rw [← hr]
      exact inv_eq_of_mul_eq_one_right (hsq r)
    rw [hi]
    exact ⟨flipIndex k i r, hr ▸ hstep i r⟩

public theorem square_of_table (k : Fin 8)
    (h : ∀ r : Fin (dim k), ∀ v : Fin 4,
      rowTable (row k) r.val (rowTable (row k) r.val ⟨v.val, by omega⟩) = ⟨v.val, by omega⟩) :
    ∀ r : Fin (dim k), rowElement (row k) r.val * rowElement (row k) r.val = 1 := by
  intro r
  apply Held.eq_of_four_point_images
  intro v
  simpa only [rowTable_eq, map_mul, map_one, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h r v

public theorem transition_of_table (k : Fin 8)
    (h : ∀ i : Fin (2 ^ dim k), ∀ r : Fin (dim k), ∀ v : Fin 4,
      normalTable k i (rowTable (row k) r.val ⟨v.val, by omega⟩) =
        normalTable k (flipIndex k i r) ⟨v.val, by omega⟩) :
    ∀ i r, normalForm k i * rowElement (row k) r.val =
      normalForm k (flipIndex k i r) := by
  intro i r
  apply Held.eq_of_four_point_images
  intro v
  simpa only [normalTable_eq, rowTable_eq, map_mul, Equiv.Perm.mul_apply] using h i r v

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment
open ProperInclusions

/-- The small certificate interface: closure transitions and permutation
signatures. All data refer to the original row words. -/
public theorem signature_package (k : Fin 8) (partner : Fin (2 ^ dim k) → Fin (2 ^ dim k))
    (hsq : ∀ r : Fin (dim k), rowElement (row k) r.val * rowElement (row k) r.val = 1)
    (hstep : ∀ i r, normalForm k i * rowElement (row k) r.val = normalForm k (flipIndex k i r))
    (hcount : tableCommonCount (normalTable k (centralIndex k))
      (normalTable k (centralIndex k)) = 42)
    (havoid : ∀ i, tableCommonCount (normalTable k (centralIndex k)) (normalTable k i) ≠ bad k)
    (helim : ∀ i, i = centralIndex k ∨ tableCommonCount (normalTable k i) (normalTable k i) ≠ 42 ∨
      tableCommonCount (normalTable k i) (normalTable k (partner i)) = bad k) :
    Signature (row k) (bad k) centralWord ∧
      ∀ x, Signature (row k) (bad k) x → x = centralWord := by
  have hcover := cover_of_transitions k hsq hstep
  constructor
  · apply signature_of_cover (normalForm k) hcover (centralWord_mem k)
    · rwa [← normalForm_central k, normal_count_eq]
    · intro i
      rw [← normalForm_central k, normal_count_eq]
      exact havoid i
  · apply signature_unique_of_cover (normalForm k) hcover
    intro i
    rcases helim i with hi | hi | hi
    · exact Or.inl (hi ▸ normalForm_central k)
    · exact Or.inr (Or.inl (by rwa [normal_count_eq]))
    · exact Or.inr (Or.inr ⟨partner i, normalForm_mem _ _, by rwa [normal_count_eq]⟩)

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment
