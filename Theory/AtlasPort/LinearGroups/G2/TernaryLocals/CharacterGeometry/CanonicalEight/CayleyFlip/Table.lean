module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.CanonicalEight.CayleyProducts
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.CanonicalEight.CayleyFlip.Identities

/-!
# The binary grading of an orthogonal Cayley frame

For `(1,a,b,ab,c,ac,bc,(ab)c)`, the product of two frame vectors is a
scalar multiple of the vector indexed by the xor of their indices.
Orthogonality gives tracelessness and anticommutation. Polarized
alternativity supplies the three-generator signs, and the middle Moufang
identity handles products of composite generators. Bilinearity then makes
any character of this binary grading multiplicative on the whole algebra.

The calculation uses the concrete licensed ATLAS octonion table,
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff, Wilson Eq. (4.11).
Application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(4), printed pp.3–4 and 481–482.
-/

@[expose] public section

open Atlas.SplitOctonion
namespace Atlas.G2.TernaryLocals.CharacterGeometry.CanonicalEight

private theorem mul_neg' (x y : V) : mul x (-y) = -mul x y :=
  (multiplication x).map_neg y
private theorem neg_mul' (x y : V) : mul (-x) y = -mul x y :=
  (multiplication.flip y).map_neg x

def flipIndex (i j : Fin 8) : Fin 8 := Fin.ofNat 8 (Nat.xor i.val j.val)

private theorem flip_mul_line_lt (a b c : V)
    (ho : ∀ i j, i ≠ j → normPolar (cayleyProducts a b c i)
      (cayleyProducts a b c j) = 0)
    (i j : Fin 8) (hi : 0 < i) (hij : i < j) :
    ∃ r : ZMod 3, mul (cayleyProducts a b c i) (cayleyProducts a b c j) =
      r • cayleyProducts a b c (flipIndex i j) := by
  have ht (k : Fin 8) (hk : k ≠ 0) : trace (cayleyProducts a b c k) = 0 := by
    rw [← flip_polar_unit]
    exact ho 0 k (Ne.symm hk)
  have hs (k l : Fin 8) (hk : k ≠ 0) (hl : l ≠ 0) (hkl : k ≠ l) :
      mul (cayleyProducts a b c k) (cayleyProducts a b c l) =
        -mul (cayleyProducts a b c l) (cayleyProducts a b c k) :=
    flip_skew _ _ (ht k hk) (ht l hl) (ho k l hkl)
  have hl (k : Fin 8) (hk : k ≠ 0) (x : V) :
      mul (cayleyProducts a b c k) (mul (cayleyProducts a b c k) x) =
        -norm (cayleyProducts a b c k) • x := by
    simpa [ht k hk] using flip_left_square (cayleyProducts a b c k) x
  have h13 : mul a (mul a b) = -norm a • b := hl 1 (by decide) b
  have h15 : mul a (mul a c) = -norm a • c := hl 1 (by decide) c
  have h26 : mul b (mul b c) = -norm b • c := hl 2 (by decide) c
  have s12 : mul a b = -mul b a := hs 1 2 (by decide) (by decide) (by decide)
  have s21 : mul b a = -mul a b := hs 2 1 (by decide) (by decide) (by decide)
  have s41 : mul c a = -mul a c := hs 4 1 (by decide) (by decide) (by decide)
  have s42 : mul c b = -mul b c := hs 4 2 (by decide) (by decide) (by decide)
  have s43 : mul c (mul a b) = -mul (mul a b) c :=
    hs 4 3 (by decide) (by decide) (by decide)
  have h16 : mul a (mul b c) = -mul (mul a b) c := by
    have h := flip_left_skew a c b (ht 1 (by decide)) (ht 4 (by decide))
      (ho 1 4 (by decide))
    rw [s42, mul_neg', s43, neg_neg] at h
    exact neg_eq_iff_eq_neg.mp h
  have h25 : mul b (mul a c) = mul (mul a b) c := by
    have h := flip_left_skew b a c (ht 2 (by decide)) (ht 1 (by decide))
      (ho 2 1 (by decide))
    simpa [h16] using h
  have h23 : mul b (mul a b) = norm b • a := by
    rw [s12, mul_neg']
    simpa [cayleyProducts] using congrArg Neg.neg (hl 2 (by decide) a)
  have h45 : mul c (mul a c) = norm c • a := by
    have s14 : mul a c = -mul c a := hs 1 4 (by decide) (by decide) (by decide)
    rw [s14, mul_neg']
    simpa [cayleyProducts] using congrArg Neg.neg (hl 4 (by decide) a)
  have h46 : mul c (mul b c) = norm c • b := by
    have s24 : mul b c = -mul c b := hs 2 4 (by decide) (by decide) (by decide)
    rw [s24, mul_neg']
    simpa [cayleyProducts] using congrArg Neg.neg (hl 4 (by decide) b)
  have h47 : mul c (mul (mul a b) c) = norm c • mul a b := by
    have s34 : mul (mul a b) c = -mul c (mul a b) :=
      hs 3 4 (by decide) (by decide) (by decide)
    rw [s34, mul_neg']
    simpa [cayleyProducts] using congrArg Neg.neg (hl 4 (by decide) (mul a b))
  have h17 : mul a (mul (mul a b) c) = norm a • mul b c := by
    have hd : mul (mul a b) c = -mul a (mul b c) := by rw [h16, neg_neg]
    rw [hd, mul_neg']
    simpa [cayleyProducts] using congrArg Neg.neg (hl 1 (by decide) (mul b c))
  have h27 : mul b (mul (mul a b) c) = -norm b • mul a c := by
    rw [← h25]
    exact hl 2 (by decide) (mul a c)
  have h35 : mul (mul a b) (mul a c) = -norm a • mul b c := by
    have s61 : mul (mul b c) a = mul (mul a b) c := by
      have h := hs 6 1 (by decide) (by decide) (by decide)
      change mul (mul b c) a = -mul a (mul b c) at h
      simpa [h16] using h
    have h := flip_moufang a b c
    rw [s41, mul_neg', s61, h17] at h
    simpa using congrArg Neg.neg h
  have h36 : mul (mul a b) (mul b c) = norm b • mul a c := by
    have s52 : mul (mul a c) b = -mul b (mul a c) :=
      hs 5 2 (by decide) (by decide) (by decide)
    have h := flip_moufang b a c
    rw [s21, s42, neg_mul', mul_neg', neg_neg, s52, h25, mul_neg', h27] at h
    simpa using h
  have h37 : mul (mul a b) (mul (mul a b) c) = -norm (mul a b) • c :=
    hl 3 (by decide) c
  have h56 : mul (mul a c) (mul b c) = -norm c • mul a b := by
    have h := flip_moufang c a b
    rw [s41, neg_mul', h47] at h
    simpa using congrArg Neg.neg h
  have h57 : mul (mul a c) (mul (mul a b) c) = (norm a * norm c) • b := by
    have h := flip_moufang c a (mul a b)
    rw [s41, neg_mul', h13, smul_mul, SplitOctonion.mul_smul, h46, smul_smul] at h
    simpa using congrArg Neg.neg h
  have h67 : mul (mul b c) (mul (mul a b) c) = -(norm b * norm c) • a := by
    have h := flip_moufang c b (mul a b)
    rw [s42, neg_mul', h23, smul_mul, SplitOctonion.mul_smul, h45, smul_smul] at h
    simpa using congrArg Neg.neg h
  clear ho ht hs hl s12 s21 s41 s42 s43
  change 0 < i.val at hi
  change i.val < j.val at hij
  fin_cases i <;> fin_cases j
  all_goals norm_num at hi
  all_goals norm_num at hij
  · exact ⟨1, (one_smul _ _).symm⟩
  · exact ⟨_, h13⟩
  · exact ⟨1, (one_smul _ _).symm⟩
  · exact ⟨_, h15⟩
  · exact ⟨-1, h16.trans (neg_one_smul (ZMod 3) _).symm⟩
  · exact ⟨_, h17⟩
  · exact ⟨_, h23⟩
  · exact ⟨1, (one_smul _ _).symm⟩
  · exact ⟨1, h25.trans (one_smul (ZMod 3) _).symm⟩
  · exact ⟨_, h26⟩
  · exact ⟨_, h27⟩
  · exact ⟨1, (one_smul _ _).symm⟩
  · exact ⟨_, h35⟩
  · exact ⟨_, h36⟩
  · exact ⟨_, h37⟩
  · exact ⟨_, h45⟩
  · exact ⟨_, h46⟩
  · exact ⟨_, h47⟩
  · exact ⟨_, h56⟩
  · exact ⟨_, h57⟩
  · exact ⟨_, h67⟩

@[simp] theorem flipIndex_zero_left (i : Fin 8) : flipIndex 0 i = i :=
  (by decide +kernel : ∀ i, flipIndex 0 i = i) i

@[simp] theorem flipIndex_zero_right (i : Fin 8) : flipIndex i 0 = i :=
  (by decide +kernel : ∀ i, flipIndex i 0 = i) i

@[simp] theorem flipIndex_self (i : Fin 8) : flipIndex i i = 0 :=
  (by decide +kernel : ∀ i, flipIndex i i = 0) i

theorem flipIndex_comm (i j : Fin 8) : flipIndex i j = flipIndex j i :=
  (by decide +kernel : ∀ i j, flipIndex i j = flipIndex j i) i j

/-- The parity character is multiplicative on the binary index group. -/
theorem firstSign_flipIndex (i j : Fin 8) :
    firstSign (flipIndex i j) = firstSign i * firstSign j :=
  (by decide +kernel : ∀ i j,
    firstSign (flipIndex i j) = firstSign i * firstSign j) i j

/-- Products in any orthogonal Cayley frame lie on the line indexed by xor.
This follows from the concrete alternative and Moufang identities; it is
not a consequence merely of orthogonality of an arbitrary eight-tuple. -/
theorem cayleyProducts_mul_line (a b c : V)
    (ho : ∀ i j, i ≠ j → normPolar (cayleyProducts a b c i)
      (cayleyProducts a b c j) = 0) (i j : Fin 8) :
    ∃ r : ZMod 3, mul (cayleyProducts a b c i) (cayleyProducts a b c j) =
      r • cayleyProducts a b c (flipIndex i j) := by
  have ht (k : Fin 8) (hk : k ≠ 0) : trace (cayleyProducts a b c k) = 0 := by
    rw [← flip_polar_unit]
    exact ho 0 k (Ne.symm hk)
  by_cases hi : i = 0
  · subst i
    rw [flipIndex_zero_left]
    exact ⟨1, (unit_mul _).trans (one_smul _ _).symm⟩
  by_cases hj : j = 0
  · subst j
    rw [flipIndex_zero_right]
    exact ⟨1, (mul_unit _).trans (one_smul _ _).symm⟩
  by_cases hij : i = j
  · subst j
    rw [flipIndex_self]
    exact ⟨-norm (cayleyProducts a b c i), flip_square _ (ht i hi)⟩
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact flip_mul_line_lt a b c ho i j (by omega) hij
  · obtain ⟨r, hr⟩ := flip_mul_line_lt a b c ho j i (by omega) hji
    refine ⟨-r, ?_⟩
    rw [flip_skew _ _ (ht i hi) (ht j hj) (ho i j hij), hr, flipIndex_comm j i]
    simp

end Atlas.G2.TernaryLocals.CharacterGeometry.CanonicalEight
