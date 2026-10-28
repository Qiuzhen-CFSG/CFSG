module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.SmallDegrees.Arithmetic.Catalogue

/-!
# Exhausting triples of exceptional constituents

After normalizing a constituent by its coefficient, the degree and Gram sums
recover the third row from the first two. The finite certificates test the
remaining local constraints and an integer form of the Suzuki equation.
The second induction also uses the first induction's forced coefficient rows.
Repeated numerical rows are permitted in every enumeration.
Source: Janko (1968), Sections 6--7, omitted calculation on p.16.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees.Arithmetic
open CharacterOrder
@[expose] public def targetDegree (i : Fin 5) : ℤ := -exceptionalCoefficients i 0
@[expose] public def targetGram (i l : Fin 5) : ℤ :=
  exceptionalGram i l - exceptionalCoefficients i 0 * exceptionalCoefficients l 0
@[expose] public def targetSuzuki (i : Fin 5) : ℚ :=
  pairingConstants i * (128 / 385) - exceptionalCoefficients i 0
@[expose] public def weight (r : SignedRow) : ℚ := (columnValue r.2 0 : ℚ)^2 / r.1
@[expose] public def remainder (i : Fin 5) (a b : SignedRow) : SignedRow :=
  (targetDegree i - a.1 - b.1, fun l => targetGram i l - a.2 l - b.2 l)
@[expose] public def Triple (i : Fin 5) (a b c : SignedRow) : Prop :=
  a.1 + b.1 + c.1 = targetDegree i ∧
  (∀ l, a.2 l + b.2 l + c.2 l = targetGram i l) ∧
  weight a + weight b + weight c = targetSuzuki i
@[expose] public def forced2 : List SignedRow :=
  [(55, ![0,-1,1,0,0]), (154, ![1,1,1,1,0]), (-210, ![0,0,1,0,-1])]
@[expose] public def forced0 : List SignedRow :=
  [(231, ![1,0,0,0,0]), (-385, ![1,0,0,-1,0]), (154, ![1,1,1,1,0])]
@[expose] public def forced1 : List SignedRow :=
  [(-55, ![0,1,-1,0,0]), (154, ![1,1,1,1,0]), (-99, ![0,1,0,0,1])]

@[expose] public def firstCompatible (r : SignedRow) : Prop :=
  r.2 0 = 0 ∨ (r.2 0 * r.1, fun l => r.2 0 * r.2 l) ∈ forced0
public instance (r : SignedRow) : Decidable (firstCompatible r) :=
  inferInstanceAs (Decidable (_ ∨ _))
@[expose] public def finalRows1 : List SignedRow :=
  signedRows1.filter (fun r => decide (firstCompatible r))
public theorem signed_mem_one_final : ∀ r ∈ rows,
    r.2 1 ≠ 0 → (r.2 2 = 0 ∨ r.1 = 55 ∨ r.1 = 154 ∨ r.1 = 210) →
    (r.2 0 = 0 ∨ r = (231, ![1,0,0,0,0]) ∨ r = (385, ![-1,0,0,1,0]) ∨
      r = (154, ![1,1,1,1,0])) → signed 1 r ∈ finalRows1 := by decide +kernel

private def possible (r : SignedRow) : Prop :=
  r.1 ≠ 0 ∧ r.1.natAbs ≤ 665 ∧ r.1.natAbs ∣ 443520 ∧
  (∀ i, r.2 i = 0 ∨ r.2 i = 1 ∨ r.2 i = -1) ∧
  (128 : ℤ) ∣ r.1 + 153 * r.2 0 - 202 * r.2 1 + 127 * r.2 2 +
    280 * r.2 3 + 45 * r.2 4 ∧
  (if 0 < r.1 then 0 ≤ r.1 + 15 * columnValue r.2 0 ∧ columnValue r.2 0 < r.1
    else r.1 + 15 * columnValue r.2 0 ≤ 0 ∧ r.1 < columnValue r.2 0)
private instance (r : SignedRow) : Decidable (possible r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
private def cleared (q n : ℤ) (a b c : SignedRow) : Prop :=
  q * (columnValue a.2 0 ^ 2 * b.1 * c.1 +
    columnValue b.2 0 ^ 2 * a.1 * c.1 + columnValue c.2 0 ^ 2 * a.1 * b.1) =
    n * a.1 * b.1 * c.1
private instance (q n : ℤ) (a b c : SignedRow) : Decidable (cleared q n a b c) :=
  inferInstanceAs (Decidable (_ = _))
private def compatible (r : SignedRow) : Prop :=
  r.2 2 = 0 ∨ r.1.natAbs = 55 ∨ r.1.natAbs = 154 ∨ r.1.natAbs = 210
private instance (r : SignedRow) : Decidable (compatible r) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
private theorem possible_zero : ∀ r ∈ signedRows0, possible r ∧ compatible r := by decide +kernel
private theorem possible_one : ∀ r ∈ finalRows1, possible r ∧ compatible r ∧ firstCompatible r := by decide +kernel
private theorem possible_two : ∀ r ∈ signedRows2, possible r := by decide +kernel

private theorem check_two : ∀ a ∈ signedRows2, ∀ b ∈ signedRows2,
    possible (remainder 2 a b) →
    cleared 1155 (1757) a b (remainder 2 a b) → a ∈ forced2 := by
  decide +kernel
private theorem check_zero : ∀ a ∈ signedRows0, ∀ b ∈ signedRows0,
    (possible (remainder 0 a b) ∧ compatible (remainder 0 a b)) →
    cleared 1155 (992) a b (remainder 0 a b) → a ∈ forced0 := by
  decide +kernel
private theorem check_one : ∀ a ∈ finalRows1, ∀ b ∈ finalRows1,
    (possible (remainder 1 a b) ∧ compatible (remainder 1 a b) ∧ firstCompatible (remainder 1 a b)) →
    cleared 385 (-128) a b (remainder 1 a b) → a ∈ forced1 := by
  decide +kernel

private theorem clear_weight {a b c : SignedRow} {q n : ℤ}
    (ha : a.1 ≠ 0) (hb : b.1 ≠ 0) (hc : c.1 ≠ 0) (hq : q ≠ 0)
    (hs : weight a + weight b + weight c = (n : ℚ) / q) : cleared q n a b c := by
  have ha' : (a.1 : ℚ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b.1 : ℚ) ≠ 0 := by exact_mod_cast hb
  have hc' : (c.1 : ℚ) ≠ 0 := by exact_mod_cast hc
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  dsimp [weight] at hs
  field_simp at hs
  have hh : (q : ℚ) * ((columnValue a.2 0 : ℚ)^2 * b.1 * c.1 +
      (columnValue b.2 0 : ℚ)^2 * a.1 * c.1 +
      (columnValue c.2 0 : ℚ)^2 * a.1 * b.1) =
      (n : ℚ) * a.1 * b.1 * c.1 := by
    nlinarith [hs]
  exact_mod_cast hh

private theorem third_eq_remainder (i : Fin 5) {a b c : SignedRow} (h : Triple i a b c) :
    c = remainder i a b := by
  apply Prod.ext
  · dsimp [remainder]; have := h.1; omega
  · funext l; dsimp [remainder]; have := h.2.1 l; omega

public theorem triple_two {a b c : SignedRow} (ha : a ∈ signedRows2)
    (hb : b ∈ signedRows2) (hc : c ∈ signedRows2) (h : Triple 2 a b c) : a ∈ forced2 := by
  have hs : weight a + weight b + weight c = (1757 : ℚ) / 1155 := by
    have ht := h.2.2
    simp [targetSuzuki, pairingConstants, exceptionalCoefficients] at ht
    norm_num at ht ⊢
    exact ht
  have he := clear_weight (possible_two _ ha).1 (possible_two _ hb).1
    (possible_two _ hc).1 (show (1155 : ℤ) ≠ 0 by decide) hs
  rw [third_eq_remainder 2 h] at hc he
  exact check_two a ha b hb (possible_two _ hc) he
public theorem triple_zero {a b c : SignedRow} (ha : a ∈ signedRows0)
    (hb : b ∈ signedRows0) (hc : c ∈ signedRows0) (h : Triple 0 a b c) : a ∈ forced0 := by
  have hs : weight a + weight b + weight c = (992 : ℚ) / 1155 := by
    have ht := h.2.2
    simp [targetSuzuki, pairingConstants, exceptionalCoefficients] at ht
    norm_num at ht ⊢
    exact ht
  have he := clear_weight (possible_zero _ ha).1.1 (possible_zero _ hb).1.1
    (possible_zero _ hc).1.1 (show (1155 : ℤ) ≠ 0 by decide) hs
  rw [third_eq_remainder 0 h] at hc he
  exact check_zero a ha b hb (possible_zero _ hc) he
public theorem triple_one {a b c : SignedRow} (ha : a ∈ finalRows1)
    (hb : b ∈ finalRows1) (hc : c ∈ finalRows1) (h : Triple 1 a b c) : a ∈ forced1 := by
  have hs : weight a + weight b + weight c = (-128 : ℚ) / 385 := by
    have ht := h.2.2
    simp [targetSuzuki, pairingConstants, exceptionalCoefficients] at ht
    norm_num at ht ⊢
    exact ht
  have he := clear_weight (possible_one _ ha).1.1 (possible_one _ hb).1.1
    (possible_one _ hc).1.1 (show (385 : ℤ) ≠ 0 by decide) hs
  rw [third_eq_remainder 1 h] at hc he
  exact check_one a ha b hb (possible_one _ hc) he
end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees.Arithmetic
