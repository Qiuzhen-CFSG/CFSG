module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.ArithmeticChecks

/-!
# Certified arithmetic of the marked Sylow normal forms

Every stored fingerprint and every inverse decoding entry is checked. Existing
normal-form surjectivity then proves multiplication for arbitrary pairs, using
only two forward evaluations. There is no 2048-by-2048 multiplication-table
assumption. Word induction recovers actual seed members from positive words;
the final equation lemma uses exactly q*u = v*n with left products.

Source: Parrott (1972), section 5, p.683; the certified Atlas normal forms and
`source/README.md`. Blocks of 64 keep each kernel check small.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates

theorem fingerprint_zero (n : Fin 2048) : fingerprint n false = normalMap n 0 := by
  have h := arithmetic_checks n
  simp only [arithmeticTest, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

theorem fingerprint_second (n : Fin 2048) : fingerprint n true = normalMap n 930 := by
  have h := arithmetic_checks n
  simp only [arithmeticTest, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

theorem decode_normalMap (n : Fin 2048) :
    decode (normalMap n 0) (normalMap n 930) = n := by
  have h := arithmetic_checks n
  simp only [arithmeticTest, Bool.and_eq_true, beq_iff_eq] at h
  rw [← h.1.1, ← h.1.2]
  exact h.2

/-- The decoder recovers every actual element of the marked Sylow subgroup. -/
theorem decode_sound (x : Atlas1600Group) (hx : x ∈ atlas1600SylowTwoSubgroup) :
    atlas1600SylowTwoNormalForm (decode (x.val 0) (x.val 930)) = x := by
  obtain ⟨n, rfl⟩ := atlas1600SylowTwoNormalForm_surjective hx
  rw [← normalMap_apply, ← normalMap_apply, decode_normalMap]

private theorem value_mul (x y : Atlas1600Group) : (x * y).val = x.val * y.val := rfl

/-- All multiplication equations, with no finite table premise. -/
theorem normalMul_sound (a b : Fin 2048) :
    atlas1600SylowTwoNormalForm (normalMul a b) =
      atlas1600SylowTwoNormalForm a * atlas1600SylowTwoNormalForm b := by
  have h := decode_sound (atlas1600SylowTwoNormalForm a * atlas1600SylowTwoNormalForm b)
    (atlas1600SylowTwoSubgroup.mul_mem (atlas1600SylowTwoNormalForm_mem a)
      (atlas1600SylowTwoNormalForm_mem b))
  simpa only [normalMul, fingerprint_zero, fingerprint_second, normalMap_apply,
    value_mul, Equiv.Perm.mul_apply] using h

def normalWord : List (Fin 2048) → Fin 2048
  | [] => 0
  | a :: w => normalMul a (normalWord w)

theorem normalWord_sound (w : List (Fin 2048)) :
    atlas1600SylowTwoNormalForm (normalWord w) = seedWord w := by
  induction w with
  | nil => simp [normalWord, seedWord, atlas1600SylowTwoNormalForm_eq]
  | cons a w ih =>
    rw [normalWord, normalMul_sound, ih]
    rfl

/-- Positive generator words certify membership in the literal seed. -/
theorem normalForm_mem_of_word (i : Fin 122) (q : Fin 2048) (w : List (Fin 2048))
    (hw : ∀ n ∈ w, n ∈ seedIndices i) (hq : normalWord w = q) :
    atlas1600SylowTwoNormalForm q ∈ seed i := by
  rw [← hq, normalWord_sound]
  exact seedWord_mem i w hw

/-- Numeric recovery equations have precisely the required multiplication order. -/
theorem recovery_of_normalMul (i : Fin 122) (a b : Fin 32) (q n : Fin 2048)
    (h : normalMul q (transversalPattern (seedTransversalPattern i) a) =
      normalMul (transversalPattern (seedTransversalPattern i) b) n) :
    atlas1600SylowTwoNormalForm q * transversal i a =
      transversal i b * atlas1600SylowTwoNormalForm n := by
  simpa only [normalMul_sound, transversal] using congrArg atlas1600SylowTwoNormalForm h

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates
