module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ExtraExtensions.Cohomology.Linear

/-!
# Coordinates for the binary S4 cohomology calculation

The lexicographic list of permutations fixes all indices in the certificates.
The multiplication table is verified against left permutation composition.
Binary masks denote linear forms in the 2304 (including normalized-zero) cocycle coordinates.
These are auxiliary coordinates for Huppert--Blackburn III, XII.1.18(b), p.314.
-/

@[expose] public section
namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions.Cohomology
open LocalModelDichotomy
open scoped BigOperators

def permutationTable : Fin 24 → Fin 4 → Fin 4 := ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 2, 3, 1], ![0, 3, 1, 2], ![0, 3, 2, 1], ![1, 0, 2, 3], ![1, 0, 3, 2], ![1, 2, 0, 3], ![1, 2, 3, 0], ![1, 3, 0, 2], ![1, 3, 2, 0], ![2, 0, 1, 3], ![2, 0, 3, 1], ![2, 1, 0, 3], ![2, 1, 3, 0], ![2, 3, 0, 1], ![2, 3, 1, 0], ![3, 0, 1, 2], ![3, 0, 2, 1], ![3, 1, 0, 2], ![3, 1, 2, 0], ![3, 2, 0, 1], ![3, 2, 1, 0]]

def inverseTable : Fin 24 → Fin 24 := ![0, 1, 2, 4, 3, 5, 6, 7, 12, 18, 13, 19, 8, 10, 14, 20, 16, 22, 9, 11, 15, 21, 17, 23]

def element (s : Fin 24) : SymmetricFour where
  toFun := permutationTable s
  invFun := permutationTable (inverseTable s)
  left_inv := (by decide +kernel : ∀ s i, permutationTable (inverseTable s) (permutationTable s i) = i) s
  right_inv := (by decide +kernel : ∀ s i, permutationTable s (permutationTable (inverseTable s) i) = i) s

def index (s : SymmetricFour) : Fin 24 :=
  match permutationCode s with
  | 27 => 0
  | 30 => 1
  | 39 => 2
  | 45 => 3
  | 54 => 4
  | 57 => 5
  | 75 => 6
  | 78 => 7
  | 99 => 8
  | 108 => 9
  | 114 => 10
  | 120 => 11
  | 135 => 12
  | 141 => 13
  | 147 => 14
  | 156 => 15
  | 177 => 16
  | 180 => 17
  | 198 => 18
  | 201 => 19
  | 210 => 20
  | 216 => 21
  | 225 => 22
  | 228 => 23
  | _ => 0

def product : Fin 24 → Fin 24 → Fin 24 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], ![1, 0, 4, 5, 2, 3, 7, 6, 10, 11, 8, 9, 18, 19, 20, 21, 22, 23, 12, 13, 14, 15, 16, 17], ![2, 3, 0, 1, 5, 4, 12, 13, 14, 15, 16, 17, 6, 7, 8, 9, 10, 11, 19, 18, 22, 23, 20, 21], ![3, 2, 5, 4, 0, 1, 13, 12, 16, 17, 14, 15, 19, 18, 22, 23, 20, 21, 6, 7, 8, 9, 10, 11], ![4, 5, 1, 0, 3, 2, 18, 19, 20, 21, 22, 23, 7, 6, 10, 11, 8, 9, 13, 12, 16, 17, 14, 15], ![5, 4, 3, 2, 1, 0, 19, 18, 22, 23, 20, 21, 13, 12, 16, 17, 14, 15, 7, 6, 10, 11, 8, 9], ![6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 14, 15, 12, 13, 17, 16, 20, 21, 18, 19, 23, 22], ![7, 6, 10, 11, 8, 9, 1, 0, 4, 5, 2, 3, 20, 21, 18, 19, 23, 22, 14, 15, 12, 13, 17, 16], ![8, 9, 6, 7, 11, 10, 14, 15, 12, 13, 17, 16, 0, 1, 2, 3, 4, 5, 21, 20, 23, 22, 18, 19], ![9, 8, 11, 10, 6, 7, 15, 14, 17, 16, 12, 13, 21, 20, 23, 22, 18, 19, 0, 1, 2, 3, 4, 5], ![10, 11, 7, 6, 9, 8, 20, 21, 18, 19, 23, 22, 1, 0, 4, 5, 2, 3, 15, 14, 17, 16, 12, 13], ![11, 10, 9, 8, 7, 6, 21, 20, 23, 22, 18, 19, 15, 14, 17, 16, 12, 13, 1, 0, 4, 5, 2, 3], ![12, 13, 14, 15, 16, 17, 2, 3, 0, 1, 5, 4, 8, 9, 6, 7, 11, 10, 22, 23, 19, 18, 21, 20], ![13, 12, 16, 17, 14, 15, 3, 2, 5, 4, 0, 1, 22, 23, 19, 18, 21, 20, 8, 9, 6, 7, 11, 10], ![14, 15, 12, 13, 17, 16, 8, 9, 6, 7, 11, 10, 2, 3, 0, 1, 5, 4, 23, 22, 21, 20, 19, 18], ![15, 14, 17, 16, 12, 13, 9, 8, 11, 10, 6, 7, 23, 22, 21, 20, 19, 18, 2, 3, 0, 1, 5, 4], ![16, 17, 13, 12, 15, 14, 22, 23, 19, 18, 21, 20, 3, 2, 5, 4, 0, 1, 9, 8, 11, 10, 6, 7], ![17, 16, 15, 14, 13, 12, 23, 22, 21, 20, 19, 18, 9, 8, 11, 10, 6, 7, 3, 2, 5, 4, 0, 1], ![18, 19, 20, 21, 22, 23, 4, 5, 1, 0, 3, 2, 10, 11, 7, 6, 9, 8, 16, 17, 13, 12, 15, 14], ![19, 18, 22, 23, 20, 21, 5, 4, 3, 2, 1, 0, 16, 17, 13, 12, 15, 14, 10, 11, 7, 6, 9, 8], ![20, 21, 18, 19, 23, 22, 10, 11, 7, 6, 9, 8, 4, 5, 1, 0, 3, 2, 17, 16, 15, 14, 13, 12], ![21, 20, 23, 22, 18, 19, 11, 10, 9, 8, 7, 6, 17, 16, 15, 14, 13, 12, 4, 5, 1, 0, 3, 2], ![22, 23, 19, 18, 21, 20, 16, 17, 13, 12, 15, 14, 5, 4, 3, 2, 1, 0, 11, 10, 9, 8, 7, 6], ![23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma element_index : ∀ s, element (index s) = s := by decide +kernel

lemma index_element : ∀ s, index (element s) = s := by decide +kernel
lemma element_zero : element 0 = 1 := by decide +kernel
lemma index_one : index 1 = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma element_product : ∀ s t, element (product s t) = element s * element t := by decide +kernel

def slot (s t : Fin 24) (i : Fin 4) : Fin 2304 :=
  ⟨(s.val * 24 + t.val) * 4 + i.val, by omega⟩
def leftIndex (p : Fin 2304) : Fin 24 := ⟨p.val / 96, by omega⟩
def rightIndex (p : Fin 2304) : Fin 24 := ⟨p.val / 4 % 24, by omega⟩
def bitIndex (p : Fin 2304) : Fin 4 := ⟨p.val % 4, by omega⟩
def varMask (s t : Fin 24) (i : Fin 4) : ℕ := 2 ^ (slot s t i).val

def coordinates {α : SymmetricFour →* MulAut BinaryFour} (c : FactorSet α) :
    Fin 2304 → ZMod 2 := fun p =>
  (c.value (element (leftIndex p)) (element (rightIndex p))).toAdd (bitIndex p)

lemma left_slot (s t : Fin 24) (i : Fin 4) : leftIndex (slot s t i) = s := by
  apply Fin.ext
  simp only [leftIndex, slot]
  omega
lemma right_slot (s t : Fin 24) (i : Fin 4) : rightIndex (slot s t i) = t := by
  apply Fin.ext
  simp only [rightIndex, slot]
  omega
lemma bit_slot (s t : Fin 24) (i : Fin 4) : bitIndex (slot s t i) = i := by
  apply Fin.ext
  simp only [bitIndex, slot]
  omega
lemma slot_indices (p : Fin 2304) : slot (leftIndex p) (rightIndex p) (bitIndex p) = p := by
  apply Fin.ext
  simp only [slot, leftIndex, rightIndex, bitIndex]
  omega

lemma ev_variable {α : SymmetricFour →* MulAut BinaryFour} (c : FactorSet α)
    (s t : Fin 24) (i : Fin 4) : ev (coordinates c) (varMask s t i) =
      (c.value (element s) (element t)).toAdd i := by
  rw [varMask, ev_unit]
  simp only [coordinates, left_slot, right_slot, bit_slot]

def actMask (cols : SymmetricFour → Fin 4 → Fin 16) (s : Fin 24)
    (v : Fin 4 → ℕ) (i : Fin 4) : ℕ :=
  xorList ((List.finRange 4).map (fun j =>
    if (cols (element s) j).val.testBit i.val then v j else 0))

lemma bit_coefficient (a i : ℕ) (z : ZMod 2) :
    (if a.testBit i then z else 0) = ((a / 2 ^ i % 2 : ℕ) : ZMod 2) * z := by
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ i) with h | h <;>
    simp [Nat.testBit_eq_decide_div_mod_eq, h]

lemma ev_actMask (x : Fin 2304 → ZMod 2)
    (cols : SymmetricFour → Fin 4 → Fin 16) (s : Fin 24)
    (v : Fin 4 → ℕ) (i : Fin 4) :
    ev x (actMask cols s v i) =
      (matrixActionFun cols (element s) (Multiplicative.ofAdd (fun j => ev x (v j)))).toAdd i := by
  rw [actMask, ev_xorList, List.map_map]
  change _ = ∑ j : Fin 4, coefficientMatrix cols (element s) i j * ev x (v j)
  have hb (j : Fin 4) :
      ev x (if (cols (element s) j).val.testBit i.val then v j else 0) =
        coefficientMatrix cols (element s) i j * ev x (v j) := by
    unfold coefficientMatrix
    rw [← bit_coefficient]
    split <;> simp only [ev_zero]
  simp only [Function.comp_def, hb]
  exact (by decide +kernel : ∀ f : Fin 4 → ZMod 2,
    ((List.finRange 4).map f).sum = ∑ j, f j) _

variable {α : SymmetricFour →* MulAut BinaryFour}

def cocycleRow (cols : SymmetricFour → Fin 4 → Fin 16)
    (s t r : Fin 24) (i : Fin 4) : ℕ :=
  varMask s t i ^^^ varMask (product s t) r i ^^^
    actMask cols s (varMask t r) i ^^^ varMask s (product t r) i

lemma cocycleRow_zero (cols : SymmetricFour → Fin 4 → Fin 16)
    (ha : ∀ s v, α s v = matrixActionFun cols s v) (c : FactorSet α)
    (s t r : Fin 24) (i : Fin 4) : ev (coordinates c) (cocycleRow cols s t r i) = 0 := by
  simp only [cocycleRow, ev_xor, ev_variable, ev_actMask, element_product]
  have hc := congrArg (fun v : BinaryFour => v.toAdd i) (c.cocycle (element s) (element t) (element r))
  simp only [toAdd_mul, Pi.add_apply] at hc
  rw [ha] at hc
  rw [hc]
  exact (add_assoc _ _ _).trans (CharTwo.add_self_eq_zero _)

def rawRow (cols : SymmetricFour → Fin 4 → Fin 16) (k : ℕ) : ℕ :=
  if k < 96 then varMask 0 (Fin.ofNat 24 (k / 4)) (Fin.ofNat 4 k)
  else if k < 192 then varMask (Fin.ofNat 24 ((k - 96) / 4)) 0 (Fin.ofNat 4 k)
  else cocycleRow cols (Fin.ofNat 24 ((k - 192) / 2304))
    (Fin.ofNat 24 ((k - 192) / 96)) (Fin.ofNat 24 ((k - 192) / 4)) (Fin.ofNat 4 k)

lemma rawRow_zero (cols : SymmetricFour → Fin 4 → Fin 16)
    (ha : ∀ s v, α s v = matrixActionFun cols s v) (c : FactorSet α) (k : ℕ) :
    ev (coordinates c) (rawRow cols k) = 0 := by
  unfold rawRow
  split
  · rw [ev_variable, element_zero, c.one_left]; rfl
  · split
    · rw [ev_variable, element_zero, c.one_right]; rfl
    · exact cocycleRow_zero cols ha c _ _ _ _

/-- The linear form giving a coordinate after correcting the section. -/
def defectMask (cols : SymmetricFour → Fin 4 → Fin 16)
    (b : Fin 24 → Fin 4 → ℕ) (p : Fin 2304) : ℕ :=
  varMask (leftIndex p) (rightIndex p) (bitIndex p) ^^^
    b (leftIndex p) (bitIndex p) ^^^
    actMask cols (leftIndex p) (b (rightIndex p)) (bitIndex p) ^^^
    b (product (leftIndex p) (rightIndex p)) (bitIndex p)

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions.Cohomology
