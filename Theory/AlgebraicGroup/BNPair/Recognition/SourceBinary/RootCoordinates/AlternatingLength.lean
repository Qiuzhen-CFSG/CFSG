module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.DihedralWords

/-!
# Reduced alternating words and the longest marked Weyl element

The dihedral normal forms give the distance in the cycle with 2m vertices.
Its value changes by at most one under either original reflection, and an
alternating word of length at most m attains that value. This proves shortest
lengths in the actual Weyl quotient, a reduced alternating expression for
every element, and uniqueness of the longest element. Every other element
has a left ascent. No restriction on m beyond m ≥ 2 is used.

The longest element is an involution and either simple multiplication
shortens it by one. These are the finite rank-two word calculations used in
Carter 2.5.3–2.5.6, `refs/KGroup/GLS3/Chapter2Ca2.tex`; the subsequent
opposite-Borel proof uses the ascent chain and the split saturation axiom.
The explicit metric generalizes the fixed-parameter calculation in
`BNPair.HexagonalGeometry.Girth` without a finite computation certificate.
-/

public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates

private def cycleLength {m : ℕ} (w : DihedralGroup m) : ℕ :=
  match w with
  | .r i => min (2 * i.val) (2 * m - 2 * i.val)
  | .sr i => if i.val = 0 then 1 else min (2 * i.val - 1) (2 * m + 1 - 2 * i.val)

private def cycleSimple {m : ℕ} (b : Bool) : DihedralGroup m :=
  .sr (if b then 1 else 0)

private def cycleWord {m : ℕ} : Bool → ℕ → DihedralGroup m
  | _, 0 => 1
  | b, n + 1 => cycleSimple b * cycleWord (!b) n

private theorem cycleLength_zero_edges {m : ℕ} [NeZero m] (_hm : 2 ≤ m) (i : ZMod m) :
    cycleLength (.sr i) ≤ cycleLength (.r i) + 1 ∧
    cycleLength (.r i) ≤ cycleLength (.sr i) + 1 := by
  have hi := i.val_lt
  simp only [cycleLength]
  split_ifs <;> omega

private theorem cycleLength_one_edges {m : ℕ} [NeZero m] (hm : 2 ≤ m) (i : ZMod m) :
    cycleLength (.sr (1 + i)) ≤ cycleLength (.r i) + 1 ∧
    cycleLength (.r i) ≤ cycleLength (.sr (1 + i)) + 1 := by
  have hi := i.val_lt
  have hv : (1 : ZMod m).val = 1 := ZMod.val_one'' (by omega)
  have hadd : (1 + i).val = if i.val + 1 < m then i.val + 1 else 0 := by
    rw [ZMod.val_add, hv]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · have he : 1 + i.val = m := by omega
      rw [he, Nat.mod_self]
  by_cases h : i.val + 1 < m
  · simp only [cycleLength, hadd, if_pos h]
    rw [if_neg (by omega : i.val + 1 ≠ 0)]
    clear hadd hv
    omega
  · simp only [cycleLength, hadd, if_neg h]
    simp only [ite_true]
    clear hadd hv
    omega

private theorem cycleLength_simple_mul_le {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (b : Bool) (w : DihedralGroup m) :
    cycleLength (cycleSimple b * w) ≤ cycleLength w + 1 := by
  cases b
  · cases w with
    | r i => simpa [cycleSimple] using (cycleLength_zero_edges hm i).1
    | sr i => simpa [cycleSimple] using (cycleLength_zero_edges hm i).2
  · cases w with
    | r i => simpa [cycleSimple] using (cycleLength_one_edges hm i).1
    | sr i => simpa [cycleSimple, add_sub_cancel_left] using (cycleLength_one_edges hm (i - 1)).2

private theorem cycleWord_even_odd {m : ℕ} (k : ℕ) :
    cycleWord (m := m) false (2*k) = .r k ∧
    cycleWord (m := m) true (2*k) = .r (-(k : ZMod m)) ∧
    cycleWord (m := m) false (2*k+1) = .sr (-(k : ZMod m)) ∧
    cycleWord (m := m) true (2*k+1) = .sr (k+1) := by
  induction k with
  | zero => simp [cycleWord, cycleSimple]
  | succ k ih =>
    have he : 2 * (k+1) = (2*k+1)+1 := by omega
    simp only [he, cycleWord, cycleSimple, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, ih, DihedralGroup.sr_mul_sr, DihedralGroup.sr_mul_r,
      sub_zero, zero_add, Nat.cast_add, Nat.cast_one]
    simp only [neg_add_rev, sub_eq_add_neg, add_comm, and_self]

private theorem cycleLength_word {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (b : Bool) {n : ℕ} (hn : n ≤ m) : cycleLength (cycleWord (m := m) b n) = n := by
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Nat.even_or_odd n
  · have hn' : n = 2*k := by omega
    rw [hn'] at hn ⊢
    have hklt : k < m := by omega
    have hv : (k : ZMod m).val = k := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hklt]
    cases b
    · rw [(cycleWord_even_odd k).1]
      simp only [cycleLength, hv]
      omega
    · rw [(cycleWord_even_odd k).2.1]
      by_cases hk0 : k = 0
      · simp [hk0, cycleLength]
      · have hkn : (k : ZMod m) ≠ 0 := by intro h; have := congrArg ZMod.val h; simp [hv] at this; omega
        let : NeZero (k : ZMod m) := ⟨hkn⟩
        rw [cycleLength, ZMod.val_neg_of_ne_zero, hv]
        omega
  · have hn' : n = 2*k+1 := hk
    rw [hn'] at hn ⊢
    have hklt : k < m := by omega
    have hk1lt : k + 1 < m := by omega
    have hv : (k : ZMod m).val = k := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hklt]
    cases b
    · rw [(cycleWord_even_odd k).2.2.1]
      by_cases hk0 : k = 0
      · simp [hk0, cycleLength]
      · have hkn : (k : ZMod m) ≠ 0 := by intro h; have := congrArg ZMod.val h; simp [hv] at this; omega
        let : NeZero (k : ZMod m) := ⟨hkn⟩
        rw [cycleLength, ZMod.val_neg_of_ne_zero, hv]
        split_ifs <;> omega
    · rw [(cycleWord_even_odd k).2.2.2]
      have hv1 : ((k : ZMod m)+1).val = k+1 := by
        rw [← Nat.cast_one, ← Nat.cast_add, ZMod.val_natCast, Nat.mod_eq_of_lt hk1lt]
      simp only [cycleLength, hv1]
      rw [if_neg (by omega : k + 1 ≠ 0)]
      clear hv hv1
      omega

private theorem cycleWord_surjective {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (w : DihedralGroup m) : ∃ b k, k ≤ m ∧ cycleWord b k = w := by
  cases w with
  | r i =>
    have hi := i.val_lt
    by_cases h : 2*i.val ≤ m
    · exact ⟨false, 2*i.val, h, by rw [(cycleWord_even_odd i.val).1, ZMod.natCast_zmod_val]⟩
    · refine ⟨true, 2*(m-i.val), by omega, ?_⟩
      rw [(cycleWord_even_odd (m-i.val)).2.1]
      congr 1
      rw [Nat.cast_sub (by omega : i.val ≤ m), ZMod.natCast_self, zero_sub,
        neg_neg, ZMod.natCast_zmod_val]
  | sr i =>
    have hi := i.val_lt
    by_cases hz : i.val = 0
    · have he : i = 0 := ZMod.val_injective _ (by simpa using hz)
      exact ⟨false, 1, by omega, by simp [cycleWord, cycleSimple, he]⟩
    · by_cases h : 2*i.val-1 ≤ m
      · refine ⟨true, 2*(i.val-1)+1, by omega, ?_⟩
        rw [(cycleWord_even_odd (i.val-1)).2.2.2]
        congr 1
        rw [Nat.cast_sub (by omega : 1 ≤ i.val), Nat.cast_one, sub_add_cancel,
          ZMod.natCast_zmod_val]
      · refine ⟨false, 2*(m-i.val)+1, by omega, ?_⟩
        rw [(cycleWord_even_odd (m-i.val)).2.2.1]
        congr 1
        rw [Nat.cast_sub (by omega : i.val ≤ m), ZMod.natCast_self, zero_sub,
          neg_neg, ZMod.natCast_zmod_val]

private theorem cycleLength_le {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (w : DihedralGroup m) : cycleLength w ≤ m := by
  obtain ⟨b, k, hk, rfl⟩ := cycleWord_surjective hm w
  rw [cycleLength_word hm b hk]
  exact hk

private theorem cycleLength_max_unique {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {w v : DihedralGroup m} (hw : cycleLength w = m) (hv : cycleLength v = m) : w = v := by
  cases w with
  | r i =>
    have hi := i.val_lt
    cases v with
    | r j =>
      have hj := j.val_lt
      simp only [cycleLength] at hw hv
      congr 1
      apply ZMod.val_injective
      omega
    | sr j =>
      have hj := j.val_lt
      simp only [cycleLength] at hw hv
      split_ifs at hv <;> omega
  | sr i =>
    have hi := i.val_lt
    cases v with
    | r j =>
      have hj := j.val_lt
      simp only [cycleLength] at hw hv
      split_ifs at hw <;> omega
    | sr j =>
      have hj := j.val_lt
      simp only [cycleLength] at hw hv
      congr 1
      apply ZMod.val_injective
      split_ifs at hw hv <;> omega

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)

/-- Alternating words, with false starting at the original endpoint 0. -/
@[expose] def alternatingWord : Bool → ℕ → Weyl d
  | _, 0 => 1
  | b, n+1 => d.simple (if b then 1 else 0) * alternatingWord (!b) n

private theorem map_alternatingWord (b : Bool) (n : ℕ) :
    weylEquiv d (alternatingWord d b n) = cycleWord b n := by
  induction n generalizing b with
  | zero => simp [alternatingWord, cycleWord]
  | succ n ih => cases b <;> simp [alternatingWord, cycleWord, cycleSimple, ih]

private theorem cycleLength_le_wordLength (w : Weyl d) :
    cycleLength (weylEquiv d w) ≤ d.tits.wordLength w := by
  obtain ⟨l, hlen, hl, rfl⟩ := d.tits.wordLength_spec w
  rw [← hlen]
  clear hlen
  induction l with
  | nil =>
    simp only [List.prod_nil, map_one, List.length_nil]
    change min (2 * (0 : ZMod (rotationOrder d)).val) _ ≤ 0
    simp
  | cons s l ih =>
    obtain ⟨i, rfl⟩ := d.simple_range.symm ▸ hl s (by simp)
    have hi := ih (fun t ht => hl t (List.mem_cons_of_mem _ ht))
    fin_cases i
    · simpa [List.prod_cons, cycleSimple] using
        (cycleLength_simple_mul_le (rotationOrder_ge_two d) false (weylEquiv d l.prod)).trans
          (Nat.add_le_add_right hi 1)
    · simpa [List.prod_cons, cycleSimple] using
        (cycleLength_simple_mul_le (rotationOrder_ge_two d) true (weylEquiv d l.prod)).trans
          (Nat.add_le_add_right hi 1)

theorem wordLength_alternatingWord_le (b : Bool) (n : ℕ) :
    d.tits.wordLength (alternatingWord d b n) ≤ n := by
  induction n generalizing b with
  | zero => simp [alternatingWord, d.tits.wordLength_one]
  | succ n ih =>
    exact (d.tits.wordLength_mul_left_le (d.simple_mem _) _).trans
      (Nat.add_le_add_right (ih (!b)) 1)

/-- Every alternating word through the dihedral parameter is reduced. -/
theorem wordLength_alternatingWord (b : Bool) {n : ℕ} (hn : n ≤ rotationOrder d) :
    d.tits.wordLength (alternatingWord d b n) = n := by
  apply le_antisymm (wordLength_alternatingWord_le d b n)
  have h := cycleLength_le_wordLength d (alternatingWord d b n)
  rwa [map_alternatingWord, cycleLength_word (rotationOrder_ge_two d) b hn] at h

/-- Every Weyl element has a reduced alternating expression of length at most m. -/
theorem exists_alternatingWord (w : Weyl d) :
    ∃ b n, n ≤ rotationOrder d ∧ alternatingWord d b n = w := by
  obtain ⟨b, n, hn, he⟩ := cycleWord_surjective (rotationOrder_ge_two d) (weylEquiv d w)
  exact ⟨b, n, hn, (weylEquiv d).injective ((map_alternatingWord d b n).trans he)⟩

private theorem wordLength_eq_cycleLength (w : Weyl d) :
    d.tits.wordLength w = cycleLength (weylEquiv d w) := by
  obtain ⟨b, n, hn, rfl⟩ := exists_alternatingWord d w
  rw [wordLength_alternatingWord d b hn, map_alternatingWord,
    cycleLength_word (rotationOrder_ge_two d) b hn]

/-- The longest class is the alternating product beginning at endpoint 0. -/
@[expose] def longest : Weyl d := alternatingWord d false (rotationOrder d)

theorem wordLength_longest : d.tits.wordLength (longest d) = rotationOrder d :=
  wordLength_alternatingWord d false le_rfl

theorem wordLength_le_rotationOrder (w : Weyl d) : d.tits.wordLength w ≤ rotationOrder d := by
  rw [wordLength_eq_cycleLength]
  exact cycleLength_le (rotationOrder_ge_two d) _

/-- The longest element is unique, including the commuting m=2 case. -/
theorem eq_longest_of_wordLength_eq {w : Weyl d}
    (hw : d.tits.wordLength w = rotationOrder d) : w = longest d := by
  apply (weylEquiv d).injective
  apply cycleLength_max_unique (rotationOrder_ge_two d)
  · rwa [← wordLength_eq_cycleLength]
  · rw [← wordLength_eq_cycleLength, wordLength_longest]

theorem alternatingWord_longest (b : Bool) :
    alternatingWord d b (rotationOrder d) = longest d :=
  eq_longest_of_wordLength_eq d (wordLength_alternatingWord d b le_rfl)

/-- Every nonlongest element has a left ascent by one of the two original generators. -/
theorem exists_left_ascent {w : Weyl d} (hw : w ≠ longest d) :
    ∃ i : Fin 2, d.tits.wordLength (d.simple i * w) = d.tits.wordLength w + 1 := by
  obtain ⟨b, n, hn, rfl⟩ := exists_alternatingWord d w
  have hnlt : n < rotationOrder d := by
    have hne : n ≠ rotationOrder d := by
      intro he
      exact hw (he ▸ alternatingWord_longest d b)
    omega
  refine ⟨if !b then 1 else 0, ?_⟩
  have he : d.simple (if !b then 1 else 0) * alternatingWord d b n =
      alternatingWord d (!b) (n+1) := by simp only [alternatingWord, Bool.not_not]
  rw [he, wordLength_alternatingWord d _ (by omega), wordLength_alternatingWord d b hn]

private theorem wordLength_inv_le (w : Weyl d) :
    d.tits.wordLength w⁻¹ ≤ d.tits.wordLength w := by
  obtain ⟨l, hlen, hl, hprod⟩ := d.tits.wordLength_spec w
  have h := d.tits.wordLength_le w⁻¹ (l.map (fun x => x⁻¹)).reverse (by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ht)
    have hsS := hl s hs
    have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right
      (by simpa only [pow_two] using (d.tits.involutions s hsS).2)
    rwa [hinv]) (by rw [← List.prod_inv_reverse, hprod])
  simpa only [List.length_reverse, List.length_map, hlen] using h

theorem wordLength_inv (w : Weyl d) : d.tits.wordLength w⁻¹ = d.tits.wordLength w := by
  apply le_antisymm (wordLength_inv_le d w)
  simpa only [inv_inv] using wordLength_inv_le d w⁻¹

theorem longest_inv : (longest d)⁻¹ = longest d := by
  apply eq_longest_of_wordLength_eq d
  rw [wordLength_inv, wordLength_longest]

theorem longest_mul_self : longest d * longest d = 1 := by
  nth_rw 1 [← longest_inv d]
  exact inv_mul_cancel _

theorem wordLength_simple_mul_longest (i : Fin 2) :
    d.tits.wordLength (d.simple i * longest d) = rotationOrder d - 1 := by
  have hm : rotationOrder d = (rotationOrder d - 1) + 1 := by
    have := rotationOrder_ge_two d
    omega
  have hs (j : Fin 2) : d.simple j * d.simple j = 1 := by
    simpa only [pow_two] using (d.tits.involutions _ (d.simple_mem j)).2
  have hword (b : Bool) : longest d = d.simple (if b then 1 else 0) *
      alternatingWord d (!b) (rotationOrder d - 1) := by
    calc
      longest d = alternatingWord d b (rotationOrder d) := (alternatingWord_longest d b).symm
      _ = alternatingWord d b ((rotationOrder d - 1) + 1) := congrArg _ hm
      _ = _ := rfl
  fin_cases i
  · rw [hword false]
    change d.tits.wordLength (d.simple 0 * (d.simple 0 *
      alternatingWord d true (rotationOrder d - 1))) = _
    rw [← mul_assoc, hs, one_mul]
    exact wordLength_alternatingWord d true (Nat.sub_le _ _)
  · rw [hword true]
    change d.tits.wordLength (d.simple 1 * (d.simple 1 *
      alternatingWord d false (rotationOrder d - 1))) = _
    rw [← mul_assoc, hs, one_mul]
    exact wordLength_alternatingWord d false (Nat.sub_le _ _)

theorem wordLength_longest_mul_simple (i : Fin 2) :
    d.tits.wordLength (longest d * d.simple i) = rotationOrder d - 1 := by
  have hi : (d.simple i)⁻¹ = d.simple i := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using (d.tits.involutions _ (d.simple_mem i)).2)
  rw [← wordLength_inv d, mul_inv_rev, hi, longest_inv, wordLength_simple_mul_longest]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
