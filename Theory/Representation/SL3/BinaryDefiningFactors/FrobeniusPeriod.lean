module

public import Theory.Representation.SL3.BinaryDefiningFactors.FrobeniusPeriod.Coefficients
public import Theory.Representation.SL3.BinaryDefiningFactors.FrobeniusPeriod.RepeatedBlocks

/-!
# Frobenius rotation and the exact Schur period for SL₃ tensor words

The factors of `wordRep` occur in increasing Frobenius order. Coefficient
Frobenius therefore rotates the word to the right; `List.rotate` rotates to
the left. We first prove that left rotation cancels coefficient Frobenius on
characters, and use irreducibility to obtain an actual intertwining equivalence
with the right rotation. Uniqueness of words identifies the stabilizers.

For a binary irreducible representation modeled by such a word after extending
its actual endomorphism field, the generic Schur-period theorem identifies this
stabilizer with the multiples of the Schur degree. Thus that degree divides the
word length, and the word is a positive number of copies of a block of exactly
that length. The dimension tower gives the corresponding binary dimension.

Source: GLS III, Remark 2.8.8. The two independent catalogue assertions
(irreducibility and uniqueness) are explicit premises. No period, block formula,
nontrivial-action condition, or classification of the binary representation is
assumed here. The catalogue assembly belongs to the consumer.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
open scoped MatrixGroups TensorProduct MonoidAlgebra
namespace Representation.SL3.BinaryDefiningFactors
variable {F K : Type*} [Field F] [Field K] [CharP K 2]

variable [IsAlgClosed K]

/-- The trace formula is independent of the basis chosen for coefficient Frobenius. -/
theorem wordRep_character_frobenius_embedding (ι : F →+* K)
    (w : List Factor) (r : ℕ) (g : SL(3,F)) :
    (wordRep ((iterateFrobeniusEquiv K 2 r : K →+* K).comp ι) w).character g =
      (wordRep ι w).character g ^ (2 ^ r) :=
  wordRep_character_comp (iterateFrobeniusEquiv K 2 r) ι w g

private theorem wordRep_character_square (ι : F →+* K) (w : List Factor) (g : SL(3,F)) :
    (wordRep ((frobenius K 2).comp ι) w).character g =
      (wordRep ι w).character g ^ 2 := by
  have he : (iterateFrobeniusEquiv K 2 1 : K →+* K) = frobenius K 2 := by
    ext x
    change x ^ (2 ^ 1) = x ^ 2
    rw [pow_one]
  have h := wordRep_character_frobenius_embedding ι w 1 g
  rw [he, pow_one] at h
  exact h

private theorem character_cons (ι : F →+* K) (a : Factor) (w : List Factor)
    (g : SL(3,F)) :
    (wordRep ι (a :: w)).character g =
      (factorRep ι a).character g * (wordRep ι w).character g ^ 2 := by
  rw [wordRep_character_cons, wordRep_character_square]

private theorem character_append_singleton (ι : F →+* K) (w : List Factor)
    (a : Factor) (g : SL(3,F)) :
    (wordRep ι (w ++ [a])).character g =
      (wordRep ι w).character g * (factorRep ι a).character g ^ (2 ^ w.length) := by
  induction w with
  | nil => simp [character_cons]
  | cons b w ih =>
    simp only [List.cons_append, character_cons, ih, mul_pow, List.length_cons,
      pow_succ, pow_mul]
    ring

variable [Finite F]

private theorem embedding_frobenius_card (ι : F →+* K) (n : ℕ)
    (hcard : Nat.card F = 2 ^ n) :
    (iterateFrobeniusEquiv K 2 n : K →+* K).comp ι = ι := by
  ext x
  change (ι x) ^ (2 ^ n) = ι x
  rw [← map_pow, ← hcard]
  congr 1
  let : Fintype F := Fintype.ofFinite F
  simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card x

private theorem character_factor_period (ι : F →+* K) (n : ℕ)
    (hcard : Nat.card F = 2 ^ n) (a : Factor) (g : SL(3,F)) :
    (factorRep ι a).character g ^ (2 ^ n) = (factorRep ι a).character g := by
  have h := factorRep_character_comp (iterateFrobeniusEquiv K 2 n) ι a g
  rw [embedding_frobenius_card ι n hcard] at h
  exact h.symm

private theorem character_rotate_one (ι : F →+* K) (w : List Factor)
    (hcard : Nat.card F = 2 ^ w.length) (g : SL(3,F)) :
    (wordRep ι (w.rotate 1)).character g ^ 2 = (wordRep ι w).character g := by
  cases w with
  | nil =>
    have hr := congrArg (fun v => (wordRep ι v).character g) (List.rotate_nil 1 (α := Factor))
    rw [hr, wordRep_character_nil, one_pow]
  | cons a w =>
    change Nat.card F = 2 ^ (w.length + 1) at hcard
    rw [List.rotate_cons_succ, List.rotate_zero, character_append_singleton,
      mul_pow, ← pow_mul, ← pow_succ, character_factor_period ι _ hcard,
      character_cons, mul_comm]

/-- Left rotation cancels the same number of coefficient Frobenius twists. -/
theorem wordRep_character_rotate (ι : F →+* K) (w : List Factor)
    (hcard : Nat.card F = 2 ^ w.length) (r : ℕ) (g : SL(3,F)) :
    (wordRep ι (w.rotate r)).character g ^ (2 ^ r) = (wordRep ι w).character g := by
  induction r with
  | zero =>
    rw [pow_zero, pow_one]
    exact congrArg (fun v => (wordRep ι v).character g) (List.rotate_zero w)
  | succ r ih =>
    rw [pow_succ, mul_comm (2 ^ r), pow_mul, ← List.rotate_rotate]
    rw [character_rotate_one ι _ (by simpa using hcard), ih]

/-- Frobenius sends a tensor word to its right rotation. Here `List.rotate`
rotates left, so the right rotation is expressed by `length - r % length`. -/
theorem wordRep_frobenius_equiv_rotate (ι : F →+* K) (w : List Factor)
    (hcard : Nat.card F = 2 ^ w.length)
    (hirr : ∀ v : List Factor, v.length = w.length → IsIrreducible (wordRep ι v))
    (r : ℕ) :
    Nonempty ((frobeniusConjugate 2 r (wordRep ι w)).Equiv
      (wordRep ι (w.rotate (w.length - r % w.length)))) := by
  let : IsIrreducible (wordRep ι w) := hirr w rfl
  let : IsIrreducible (frobeniusConjugate 2 r (wordRep ι w)) :=
    frobeniusConjugate_isIrreducible 2 r _
  let : IsIrreducible (wordRep ι (w.rotate (w.length - r % w.length))) :=
    hirr _ (List.length_rotate _ _)
  apply (character_eq_iff_equiv_of_irreducible _ _).mp
  funext g
  rw [character_frobeniusConjugate]
  have h := wordRep_character_rotate ι (w.rotate (w.length - r % w.length))
    (by simpa using hcard) r g
  have hr : (w.rotate (w.length - r % w.length)).rotate r = w :=
    List.rotate_eq_iff.mpr rfl
  exact (congrArg (fun v => (wordRep ι v).character g ^ (2 ^ r)) hr).symm.trans h

/-- Under uniqueness of the irreducible word catalogue, the Frobenius
stabilizer is exactly the rotation stabilizer. -/
theorem wordRep_frobenius_equiv_iff_rotate (ι : F →+* K) (w : List Factor)
    (hcard : Nat.card F = 2 ^ w.length)
    (hirr : ∀ v : List Factor, v.length = w.length → IsIrreducible (wordRep ι v))
    (hunique : ∀ u v : List Factor, u.length = w.length → v.length = w.length →
      Nonempty ((wordRep ι u).Equiv (wordRep ι v)) → u = v)
    (r : ℕ) :
    Nonempty ((wordRep ι w).Equiv (frobeniusConjugate 2 r (wordRep ι w))) ↔
      w.rotate r = w := by
  obtain ⟨e⟩ := wordRep_frobenius_equiv_rotate ι w hcard hirr r
  constructor
  · rintro ⟨f⟩
    exact List.rotate_eq_iff.mpr
      (hunique _ _ rfl (List.length_rotate _ _) ⟨f.trans e⟩)
  · intro h
    have hr := List.rotate_eq_iff.mp h
    have he : Nonempty ((wordRep ι w).Equiv
        (wordRep ι (w.rotate (w.length - r % w.length)))) := by
      rw [← hr]
      exact ⟨Representation.Equiv.refl _⟩
    exact he.map (fun f => f.trans e.symm)



section Schur
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) SL(3,F) V) [IsIrreducible ρ]
  [Algebra (Module.End (ZMod 2)[SL(3,F)] ρ.asModule) K]

/-- For an actual absolutely irreducible Schur model, word rotations have
exactly the period given by the degree of its actual endomorphism field. -/
theorem word_rotate_iff_schurDegree_dvd (ι : F →+* K) (w : List Factor)
    (hcard : Nat.card F = 2 ^ w.length)
    (hirr : ∀ v : List Factor, v.length = w.length → IsIrreducible (wordRep ι v))
    (hunique : ∀ u v : List Factor, u.length = w.length → v.length = w.length →
      Nonempty ((wordRep ι u).Equiv (wordRep ι v)) → u = v)
    (hmodel : Nonempty ((extendScalars K ρ.endFieldRep).Equiv (wordRep ι w)))
    (r : ℕ) :
    w.rotate r = w ↔ Representation.schurDegree 2 ρ ∣ r := by
  obtain ⟨e⟩ := hmodel
  let : IsIrreducible (wordRep ι w) := hirr w rfl
  let : IsIrreducible (frobeniusConjugate 2 r (wordRep ι w)) :=
    frobeniusConjugate_isIrreducible 2 r _
  let : IsAbsolutelyIrreducible ρ.endFieldRep := endFieldRep_isAbsolutelyIrreducible ρ
  let : IsIrreducible (extendScalars K ρ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension ρ.endFieldRep K
  let : IsIrreducible (frobeniusConjugate 2 r (extendScalars K ρ.endFieldRep)) :=
    frobeniusConjugate_isIrreducible 2 r _
  rw [← wordRep_frobenius_equiv_iff_rotate ι w hcard hirr hunique r,
    ← endFieldRep_frobenius_equiv_iff 2 ρ K r,
    ← character_eq_iff_equiv_of_irreducible,
    ← character_eq_iff_equiv_of_irreducible]
  simp only [funext_iff, character_frobeniusConjugate, char_iso e]

/-- The tensor word is a repeated block of exactly the Schur degree. All
period and block assertions are conclusions, not extra catalogue premises. -/
theorem exists_repeated_block_of_word_model (ι : F →+* K) (w : List Factor)
    (n : ℕ) (hn : 0 < n) (hlen : w.length = n) (hcard : Nat.card F = 2 ^ n)
    (hirr : ∀ v : List Factor, v.length = n → IsIrreducible (wordRep ι v))
    (hunique : ∀ u v : List Factor, u.length = n → v.length = n →
      Nonempty ((wordRep ι u).Equiv (wordRep ι v)) → u = v)
    (hmodel : Nonempty ((extendScalars K ρ.endFieldRep).Equiv (wordRep ι w))) :
    ∃ (t : ℕ) (b : List Factor), 0 < t ∧
      b.length = Representation.schurDegree 2 ρ ∧
      n = Representation.schurDegree 2 ρ * t ∧ w = (List.replicate t b).flatten := by
  have hp := word_rotate_iff_schurDegree_dvd ρ ι w (hlen ▸ hcard)
    (fun v hv => hirr v (hv.trans hlen))
    (fun u v hu hv => hunique u v (hu.trans hlen) (hv.trans hlen)) hmodel
  have hd : Representation.schurDegree 2 ρ ∣ n := by
    rw [← hlen]
    exact (hp w.length).mp (List.rotate_length w)
  obtain ⟨t, ht⟩ := hd
  have htpos : 0 < t := by
    by_contra h
    have : t = 0 := by omega
    simp [this] at ht
    omega
  have hsle : Representation.schurDegree 2 ρ ≤ w.length := by
    rw [hlen, ht]
    exact Nat.le_mul_of_pos_right _ htpos
  refine ⟨t, w.take (Representation.schurDegree 2 ρ), htpos, ?_, ht, ?_⟩
  · simp only [List.length_take, Nat.min_eq_left hsle]
  · exact List.eq_flatten_replicate_take_of_rotate_eq w _ t htpos (hlen.trans ht)
      ((hp _).mpr (dvd_refl _))

/-- Combining the constructed block with the dimension tower gives the
repeated-block dimension formula over the prime field. -/
theorem exists_repeated_block_dimension_of_word_model (ι : F →+* K) (w : List Factor)
    (n : ℕ) (hn : 0 < n) (hlen : w.length = n) (hcard : Nat.card F = 2 ^ n)
    (hirr : ∀ v : List Factor, v.length = n → IsIrreducible (wordRep ι v))
    (hunique : ∀ u v : List Factor, u.length = n → v.length = n →
      Nonempty ((wordRep ι u).Equiv (wordRep ι v)) → u = v)
    (hmodel : Nonempty ((extendScalars K ρ.endFieldRep).Equiv (wordRep ι w))) :
    ∃ (t : ℕ) (b : List Factor), 0 < t ∧
      b.length = Representation.schurDegree 2 ρ ∧
      n = Representation.schurDegree 2 ρ * t ∧ w = (List.replicate t b).flatten ∧
      Module.finrank (ZMod 2) V = Representation.schurDegree 2 ρ *
        (3 ^ naturalCount b * 8 ^ adjointCount b) ^ t := by
  obtain ⟨t, b, ht, hb, hn, hw⟩ :=
    exists_repeated_block_of_word_model ρ ι w n hn hlen hcard hirr hunique hmodel
  refine ⟨t, b, ht, hb, hn, hw, ?_⟩
  obtain ⟨e⟩ := hmodel
  rw [Representation.finrank_eq_schurDegree_mul 2 ρ K, e.toLinearEquiv.finrank_eq,
    finrank_wordSpace, hw, wordDegree_repeat]
end Schur

end Representation.SL3.BinaryDefiningFactors
