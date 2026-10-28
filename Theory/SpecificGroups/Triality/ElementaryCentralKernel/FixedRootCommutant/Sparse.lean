module
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRootCommutant.Coordinates

/-! Sparse multiplication by the pinned simple-root matrices. These formulas
keep the folded commutator calculation at the root-string interface. -/

@[expose] public section
namespace Triality.Standard.ElementaryCentralKernel.FixedRootCommutant

def rootRows (i : Fin 4) (s : Bool) : Fin 28 → Finset (Fin 28) :=
  if s then
    ![![{6}, ∅, ∅, ∅, ∅, {1}, ∅, ∅, {16}, {17}, ∅, ∅, {20}, {21}, ∅, ∅, ∅, ∅, {10}, {11}, ∅, ∅, {14}, {15}, ∅, ∅, ∅, ∅],
      ![∅, {18}, ∅, ∅, {8}, ∅, {10}, ∅, ∅, {5}, ∅, {7}, ∅, ∅, ∅, ∅, ∅, {0, 2, 3}, ∅, ∅, {24}, {25}, ∅, ∅, ∅, ∅, {22}, {23}],
      ![∅, ∅, {26}, ∅, ∅, ∅, ∅, ∅, {12}, ∅, {14}, ∅, ∅, {9}, ∅, {11}, {20}, ∅, {22}, ∅, ∅, {17}, ∅, {19}, ∅, {1}, ∅, ∅],
      ![∅, ∅, ∅, {27}, ∅, ∅, ∅, ∅, {13}, ∅, {15}, ∅, {9}, ∅, {11}, ∅, {21}, ∅, {23}, ∅, {17}, ∅, {19}, ∅, {1}, ∅, ∅, ∅]] i
  else
    ![![{5}, ∅, ∅, ∅, ∅, ∅, {1}, ∅, ∅, ∅, {18}, {19}, ∅, ∅, {22}, {23}, {8}, {9}, ∅, ∅, {12}, {13}, ∅, ∅, ∅, ∅, ∅, ∅],
      ![∅, {17}, ∅, ∅, ∅, {9}, ∅, {11}, {4}, ∅, {6}, ∅, ∅, ∅, ∅, ∅, ∅, ∅, {0, 2, 3}, ∅, ∅, ∅, {26}, {27}, {20}, {21}, ∅, ∅],
      ![∅, ∅, {25}, ∅, ∅, ∅, ∅, ∅, ∅, {13}, ∅, {15}, {8}, ∅, {10}, ∅, ∅, {21}, ∅, {23}, {16}, ∅, {18}, ∅, ∅, ∅, {1}, ∅],
      ![∅, ∅, ∅, {24}, ∅, ∅, ∅, ∅, ∅, {12}, ∅, {14}, ∅, {8}, ∅, {10}, ∅, {20}, ∅, {22}, ∅, {16}, ∅, {18}, ∅, ∅, ∅, {1}]] i

def rootCols (i : Fin 4) (s : Bool) : Fin 28 → Finset (Fin 28) :=
  if s then
    ![![∅, {5}, ∅, ∅, ∅, ∅, {0}, ∅, ∅, ∅, {18}, {19}, ∅, ∅, {22}, {23}, {8}, {9}, ∅, ∅, {12}, {13}, ∅, ∅, ∅, ∅, ∅, ∅],
      ![{17}, ∅, {17}, {17}, ∅, {9}, ∅, {11}, {4}, ∅, {6}, ∅, ∅, ∅, ∅, ∅, ∅, ∅, {1}, ∅, ∅, ∅, {26}, {27}, {20}, {21}, ∅, ∅],
      ![∅, {25}, ∅, ∅, ∅, ∅, ∅, ∅, ∅, {13}, ∅, {15}, {8}, ∅, {10}, ∅, ∅, {21}, ∅, {23}, {16}, ∅, {18}, ∅, ∅, ∅, {2}, ∅],
      ![∅, {24}, ∅, ∅, ∅, ∅, ∅, ∅, ∅, {12}, ∅, {14}, ∅, {8}, ∅, {10}, ∅, {20}, ∅, {22}, ∅, {16}, ∅, {18}, ∅, ∅, ∅, {3}]] i
  else
    ![![∅, {6}, ∅, ∅, ∅, {0}, ∅, ∅, {16}, {17}, ∅, ∅, {20}, {21}, ∅, ∅, ∅, ∅, {10}, {11}, ∅, ∅, {14}, {15}, ∅, ∅, ∅, ∅],
      ![{18}, ∅, {18}, {18}, {8}, ∅, {10}, ∅, ∅, {5}, ∅, {7}, ∅, ∅, ∅, ∅, ∅, {1}, ∅, ∅, {24}, {25}, ∅, ∅, ∅, ∅, {22}, {23}],
      ![∅, {26}, ∅, ∅, ∅, ∅, ∅, ∅, {12}, ∅, {14}, ∅, ∅, {9}, ∅, {11}, {20}, ∅, {22}, ∅, ∅, {17}, ∅, {19}, ∅, {2}, ∅, ∅],
      ![∅, {27}, ∅, ∅, ∅, ∅, ∅, ∅, {13}, ∅, {15}, ∅, {9}, ∅, {11}, ∅, {21}, ∅, {23}, ∅, {17}, ∅, {19}, ∅, {3}, ∅, ∅, ∅]] i

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma rootRows_check (i : Fin 4) (s : Bool) (r c : Fin 28) :
    (r, c) ∈ linearSupport i s ↔ c ∈ rootRows i s r := by
  revert i s r c
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma rootCols_check (i : Fin 4) (s : Bool) (r c : Fin 28) :
    (r, c) ∈ linearSupport i s ↔ r ∈ rootCols i s c := by
  revert i s r c
  decide +kernel

variable {F : Type*} [CommRing F]

lemma mul_root_entry (B : Matrix (Fin 28) (Fin 28) F) (i : Fin 4) (s : Bool)
    (t : F) (r c : Fin 28) :
    (B * rootMatrix i s t) r c = B r c +
      (∑ j ∈ rootCols i s c, B r j) * t +
      (if c = (quadraticPosition i s).2 then B r (quadraticPosition i s).1 * t ^ 2 else 0) := by
  simp only [Matrix.mul_apply, rootMatrix, mul_add, Finset.sum_add_distrib]
  have h₀ : (∑ j : Fin 28, B r j * (if j = c then 1 else 0)) = B r c := by simp
  have h₁ : (∑ j : Fin 28, B r j * (if (j, c) ∈ linearSupport i s then t else 0)) =
      (∑ j ∈ rootCols i s c, B r j) * t := by
    simp only [rootCols_check, mul_ite, mul_zero, Finset.sum_ite_mem_eq, Finset.sum_mul]
  have h₂ : (∑ j : Fin 28, B r j * (if (j, c) = quadraticPosition i s then t ^ 2 else 0)) =
      (if c = (quadraticPosition i s).2 then B r (quadraticPosition i s).1 * t ^ 2 else 0) := by
    by_cases hc : c = (quadraticPosition i s).2 <;> simp [Prod.ext_iff, hc, mul_ite]
  rw [h₀, h₁, h₂]

lemma root_mul_entry (B : Matrix (Fin 28) (Fin 28) F) (i : Fin 4) (s : Bool)
    (t : F) (r c : Fin 28) :
    (rootMatrix i s t * B) r c = B r c +
      t * (∑ j ∈ rootRows i s r, B j c) +
      (if r = (quadraticPosition i s).1 then t ^ 2 * B (quadraticPosition i s).2 c else 0) := by
  simp only [Matrix.mul_apply, rootMatrix, add_mul, Finset.sum_add_distrib]
  have h₀ : (∑ j : Fin 28, (if r = j then 1 else 0) * B j c) = B r c := by simp
  have h₁ : (∑ j : Fin 28, (if (r, j) ∈ linearSupport i s then t else 0) * B j c) =
      t * (∑ j ∈ rootRows i s r, B j c) := by
    simp only [rootRows_check, ite_mul, zero_mul, Finset.sum_ite_mem_eq, Finset.mul_sum]
  have h₂ : (∑ j : Fin 28, (if (r, j) = quadraticPosition i s then t ^ 2 else 0) * B j c) =
      (if r = (quadraticPosition i s).1 then t ^ 2 * B (quadraticPosition i s).2 c else 0) := by
    by_cases hr : r = (quadraticPosition i s).1 <;> simp [Prod.ext_iff, hr, ite_mul]
  rw [h₀, h₁, h₂]

end Triality.Standard.ElementaryCentralKernel.FixedRootCommutant
