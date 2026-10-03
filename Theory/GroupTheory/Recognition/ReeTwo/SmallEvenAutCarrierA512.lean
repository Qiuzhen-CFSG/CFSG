module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenAutCoordinatesA512

/-!
# The six order-512 small even candidate carriers

For candidates 0, 1, 2, 4, 5, and 6, the coordinate equations in
`SmallEvenAutCoordinatesA512` define subgroups. Their first five core coordinates
are closed under the verified polynomial multiplication, and finiteness supplies
inverses. The original generators satisfy these equations.

For the reverse inclusion, explicit binary exponent polynomials express every
parametrized point as an ordered product of the nine original generators. Both
the generator coordinates and these word identities are checked by the kernel
against `EvenCoordinates`; the polynomial tables are witnesses, not assumptions.
The resulting equivalence preserves the existing nine-coordinate convention.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified root model and the
coordinate conventions of `SmallEvenAutCoordinatesA512`.
-/

namespace ReeTwo.SylowModel
set_option maxRecDepth 16384
private theorem highBit_twice (t : ZMod 2) :
    (((2 * t.val : ZMod 4).val / 2 : ℕ) : ZMod 2) = t :=
  (by decide : ∀ t : ZMod 2, (((2 * t.val : ZMod 4).val / 2 : ℕ) : ZMod 2) = t) t
private theorem parity_twice (t : ZMod 2) :
    parity (Multiplicative.ofAdd (2 * t.val)) = 1 :=
  (by decide : ∀ t : ZMod 2, parity (Multiplicative.ofAdd (2 * t.val)) = 1) t
private theorem carrier_mul_element (i : Fin 6) (v w : Fin 9 → ZMod 2) :
    smallEvenCarrierA512 i (smallEvenElementA512 i v * smallEvenElementA512 i w) := by
  change smallEvenCarrierA512 i (evenElement (v 8) _ * evenElement (w 8) _)
  rw [evenElement_mul]
  fin_cases i <;> simp only [smallEvenCarrierA512, evenElement, parity_twice,
    true_and]
  all_goals dsimp only [Matrix.cons_val, Fin.reduceFinMk]
  all_goals split_ifs with h
  all_goals simp only [Core.mul, evenCoreAction, h, toAdd_ofAdd, highBit_twice]
  all_goals constructor <;> try ring_nf
  all_goals reduce_mod_char

private theorem carrier_mul (i : Fin 6) (x y : SylowModel)
    (hx : smallEvenCarrierA512 i x) (hy : smallEvenCarrierA512 i y) :
    smallEvenCarrierA512 i (x * y) := by
  rw [← smallEvenElementA512_parameters i x hx, ← smallEvenElementA512_parameters i y hy]
  exact carrier_mul_element i _ _
private def carrierMonoid (i : Fin 6) : Submonoid SylowModel where
  carrier := {x | smallEvenCarrierA512 i x}
  one_mem' := by fin_cases i <;> change _ ∧ _ ∧ _ <;> decide +kernel
  mul_mem' := carrier_mul i _ _
private def carrierGroup (i : Fin 6) : Subgroup SylowModel :=
  { carrierMonoid i with
    inv_mem' := fun {a} ha => show a⁻¹ ∈ carrierMonoid i by
      rw [← one_mul a⁻¹, ← pow_one a, ← pow_orderOf_eq_one a, ← pow_sub a (orderOf_pos a)]
      exact (carrierMonoid i).pow_mem ha (orderOf a - 1) }
private theorem range_nine {α : Type*} (v : Fin 9 → α) :
    Set.range v = {v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8} := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_succ, Set.mem_insert_iff, Set.mem_singleton_iff]
  simp [eq_comm]
private theorem candidate_eq_closure (i : Fin 6) :
    smallEvenCandidate (smallEvenIndexA512 i) = Subgroup.closure (Set.range (smallEvenGeneratorsA512 i)) := by
  rw [range_nine]
  fin_cases i <;> rfl

/-- Collected coordinates of the original nine generators, in their given order. -/
private def generatorData (i : Fin 6) : Fin 9 → ZMod 2 × Core :=
  (![![(1, ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩), (1, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩), (1, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩), (0, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩), (0, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩), (0, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩)],
    ![(1, ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩), (1, ⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩), (1, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩), (0, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩), (0, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩), (0, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩)],
    ![(0, ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩), (1, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩), (0, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩), (0, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩), (0, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩), (0, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩)],
    ![(0, ⟨1, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩), (1, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩), (0, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩), (0, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩), (0, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩), (0, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩)],
    ![(0, ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩), (1, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩), (0, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩), (0, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩), (0, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩), (0, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩)],
    ![(0, ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩), (1, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩), (0, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩), (0, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩), (0, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩), (0, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩), (0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩)] ]) i
private theorem generator_eq_data : ∀ i k,
    smallEvenGeneratorsA512 i k = evenElement (generatorData i k).1 (generatorData i k).2 := by
  decide +kernel
private theorem evenElement_pow_bit (t : ZMod 2) (b : Core) (z : ZMod 2) :
    evenElement t b ^ z.val = evenElement (if z = 0 then 0 else t)
      (if z = 0 then 1 else b) := by
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) z with rfl | rfl
  · exact pow_zero _
  · exact pow_one _
/-- Binary exponents recovering the nine free coordinates in each row. -/
private def exponents (i : Fin 6) (w : Fin 9 → ZMod 2) : Fin 9 → ZMod 2 :=
  (![![w 0 + w 1 + w 2,
      w 1 + w 2,
      w 0 + w 8,
      w 3 + w 0 * w 1 + w 0 * w 2,
      w 1 + w 3,
      w 3 + w 4,
      w 1 + w 3 + w 4 + w 5 + w 1 * w 2 + w 1 * w 3 + w 3 * w 8 + w 0 * w 1 * w 3 + w 0 * w 1 * w 8 + w 0 * w 2 * w 3 + w 0 * w 2 * w 8,
      w 1 + w 3 + w 4 + w 6 + w 1 * w 2 + w 3 * w 8 + w 4 * w 8,
      w 1 + w 4 + w 5 + w 6 + w 7 + w 3 * w 8 + w 4 * w 8],
    ![w 0 + w 1 + w 2,
      w 1 + w 2,
      w 0 + w 8,
      w 3 + w 0 * w 1 + w 0 * w 2,
      w 1 + w 3,
      w 3 + w 4,
      w 2 + w 3 + w 4 + w 5 + w 1 * w 2 + w 1 * w 3 + w 3 * w 8 + w 0 * w 1 * w 3 + w 0 * w 1 * w 8 + w 0 * w 2 * w 3 + w 0 * w 2 * w 8,
      w 1 + w 2 + w 3 + w 4 + w 6 + w 0 * w 1 + w 0 * w 2 + w 3 * w 8 + w 4 * w 8,
      w 4 + w 5 + w 6 + w 7 + w 1 * w 2 + w 3 * w 8 + w 4 * w 8],
    ![w 0 + w 8,
      w 8,
      w 1 + w 2,
      w 3 + w 8,
      w 1 + w 3,
      w 3 + w 4,
      w 1 + w 2 + w 3 + w 4 + w 5 + w 8 + w 1 * w 3 + w 1 * w 8,
      w 2 + w 3 + w 4 + w 6 + w 1 * w 2 + w 2 * w 8 + w 3 * w 8 + w 4 * w 8,
      w 4 + w 5 + w 6 + w 7 + w 1 * w 2 + w 3 * w 8 + w 4 * w 8],
    ![w 0,
      w 8,
      w 0 + w 3 + w 8 + w 0 * w 8,
      w 0 + w 1 + w 3 + w 0 * w 8,
      w 1 + w 2,
      w 3 + w 4,
      w 2 + w 3 + w 5 + w 8 + w 0 * w 8 + w 1 * w 3 + w 1 * w 8 + w 0 * w 1 * w 8,
      w 1 + w 3 + w 5 + w 6 + w 8 + w 0 * w 1 + w 1 * w 3 + w 3 * w 8 + w 4 * w 8 + w 0 * w 1 * w 8,
      w 0 + w 1 + w 3 + w 5 + w 6 + w 7 + w 0 * w 8 + w 1 * w 3 + w 2 * w 3 + w 3 * w 8 + w 4 * w 8],
    ![w 0 + w 1 + w 8,
      w 8,
      w 3 + w 8,
      w 0 + w 3 + w 8,
      w 0 + w 2 + w 8,
      w 3 + w 4,
      w 0 + w 2 + w 3 + w 5 + w 8 + w 0 * w 1 + w 0 * w 3 + w 0 * w 8 + w 3 * w 8,
      w 0 + w 3 + w 5 + w 6 + w 0 * w 3 + w 0 * w 8 + w 1 * w 8 + w 4 * w 8,
      w 0 + w 3 + w 5 + w 6 + w 7 + w 0 * w 3 + w 1 * w 8 + w 2 * w 3 + w 4 * w 8],
    ![w 0 + w 1,
      w 8,
      w 0,
      w 0 + w 3,
      w 2 + w 0 * w 8,
      w 0 + w 4,
      w 0 + w 2 + w 5 + w 0 * w 8 + w 3 * w 8,
      w 3 + w 4 + w 5 + w 6 + w 0 * w 1 + w 0 * w 8 + w 4 * w 8,
      w 5 + w 7 + w 0 * w 8 + w 2 * w 3 + w 0 * w 3 * w 8] ]) i
/-- The ordered product of the original generators with binary exponents. -/
private def normalWord (i : Fin 6) (w : Fin 9 → ZMod 2) : SylowModel :=
  smallEvenGeneratorsA512 i 0 ^ (w 0).val *
    smallEvenGeneratorsA512 i 1 ^ (w 1).val *
    smallEvenGeneratorsA512 i 2 ^ (w 2).val *
    smallEvenGeneratorsA512 i 3 ^ (w 3).val *
    smallEvenGeneratorsA512 i 4 ^ (w 4).val *
    smallEvenGeneratorsA512 i 5 ^ (w 5).val *
    smallEvenGeneratorsA512 i 6 ^ (w 6).val *
    smallEvenGeneratorsA512 i 7 ^ (w 7).val *
    smallEvenGeneratorsA512 i 8 ^ (w 8).val
private theorem normalWord_mem (i : Fin 6) (w : Fin 9 → ZMod 2) :
    normalWord i w ∈ smallEvenCandidate (smallEvenIndexA512 i) := by
  unfold normalWord
  repeat apply Subgroup.mul_mem
  all_goals exact Subgroup.pow_mem _ (smallEvenGeneratorsA512_mem i _) _
-- Check rows separately to bound both the heartbeat budget and peak memory.
set_option Elab.async false in
private theorem normalWord_exponents_0 : ∀ w,
    normalWord 0 (exponents 0 w) = smallEvenElementA512 0 w := by
  intro w
  simp only [normalWord, generator_eq_data, evenElement_pow_bit, evenElement_mul]
  revert w
  decide +kernel

set_option Elab.async false in
private theorem normalWord_exponents_1 : ∀ w,
    normalWord 1 (exponents 1 w) = smallEvenElementA512 1 w := by
  intro w
  simp only [normalWord, generator_eq_data, evenElement_pow_bit, evenElement_mul]
  revert w
  decide +kernel

set_option Elab.async false in
private theorem normalWord_exponents_2 : ∀ w,
    normalWord 2 (exponents 2 w) = smallEvenElementA512 2 w := by
  intro w
  simp only [normalWord, generator_eq_data, evenElement_pow_bit, evenElement_mul]
  revert w
  decide +kernel

set_option Elab.async false in
private theorem normalWord_exponents_3 : ∀ w,
    normalWord 3 (exponents 3 w) = smallEvenElementA512 3 w := by
  intro w
  simp only [normalWord, generator_eq_data, evenElement_pow_bit, evenElement_mul]
  revert w
  decide +kernel

set_option Elab.async false in
private theorem normalWord_exponents_4 : ∀ w,
    normalWord 4 (exponents 4 w) = smallEvenElementA512 4 w := by
  intro w
  simp only [normalWord, generator_eq_data, evenElement_pow_bit, evenElement_mul]
  revert w
  decide +kernel

set_option Elab.async false in
private theorem normalWord_exponents_5 : ∀ w,
    normalWord 5 (exponents 5 w) = smallEvenElementA512 5 w := by
  intro w
  simp only [normalWord, generator_eq_data, evenElement_pow_bit, evenElement_mul]
  revert w
  decide +kernel

private theorem normalWord_exponents (i : Fin 6) (w : Fin 9 → ZMod 2) :
    normalWord i (exponents i w) = smallEvenElementA512 i w := by
  fin_cases i
  · exact normalWord_exponents_0 w
  · exact normalWord_exponents_1 w
  · exact normalWord_exponents_2 w
  · exact normalWord_exponents_3 w
  · exact normalWord_exponents_4 w
  · exact normalWord_exponents_5 w

private theorem generator_carrier (i : Fin 6) (k : Fin 9) :
    smallEvenCarrierA512 i (smallEvenGeneratorsA512 i k) := by
  rw [generator_eq_data]
  fin_cases i <;> fin_cases k <;> change _ ∧ _ ∧ _ <;> decide +kernel

/-- Every point with the nine prescribed parameters lies in the original closure. -/
public theorem smallEvenElementA512_mem (i : Fin 6) (w : Fin 9 → ZMod 2) :
    smallEvenElementA512 i w ∈ smallEvenCandidate (smallEvenIndexA512 i) := by
  rw [← normalWord_exponents i w]
  exact normalWord_mem i _

/-- The original generator closures are exactly the equation-defined carriers. -/
public theorem smallEvenCandidate_mem_iff_carrierA512 (i : Fin 6) (x : SylowModel) :
    x ∈ smallEvenCandidate (smallEvenIndexA512 i) ↔ smallEvenCarrierA512 i x := by
  constructor
  · have hle : smallEvenCandidate (smallEvenIndexA512 i) ≤ carrierGroup i := by
      rw [candidate_eq_closure]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨k, rfl⟩
      exact generator_carrier i k
    intro hx
    exact hle hx
  · intro hx
    rw [← smallEvenElementA512_parameters i x hx]
    exact smallEvenElementA512_mem i _

/-- The fixed nine binary coordinates identify each original candidate with 512 points. -/
@[expose] public def smallEvenCandidateEquivA512 (i : Fin 6) :
    (Fin 9 → ZMod 2) ≃ smallEvenCandidate (smallEvenIndexA512 i) where
  toFun w := ⟨smallEvenElementA512 i w, smallEvenElementA512_mem i w⟩
  invFun x := smallEvenParametersA512 i x.val
  left_inv := smallEvenParametersA512_element i
  right_inv x := Subtype.ext (smallEvenElementA512_parameters i x.val
    ((smallEvenCandidate_mem_iff_carrierA512 i x.val).mp x.property))

@[simp] public theorem smallEvenCandidateEquivA512_apply (i : Fin 6) (w : Fin 9 → ZMod 2) :
    (smallEvenCandidateEquivA512 i w).val = smallEvenElementA512 i w := rfl

@[simp] public theorem smallEvenCandidateEquivA512_symm_apply (i : Fin 6)
    (x : smallEvenCandidate (smallEvenIndexA512 i)) :
    (smallEvenCandidateEquivA512 i).symm x = smallEvenParametersA512 i x.val := rfl

/-- Each of the six original candidates has order 512. -/
public theorem smallEvenCandidate_cardA512 (i : Fin 6) :
    Nat.card (smallEvenCandidate (smallEvenIndexA512 i)) = 512 := by
  rw [Nat.card_congr (smallEvenCandidateEquivA512 i).symm, Nat.card_fun]
  simp

end ReeTwo.SylowModel
