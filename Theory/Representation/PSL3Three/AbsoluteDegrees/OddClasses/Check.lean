module
public import Theory.SpecificGroups.PSL3Three.FiniteModel
public import Init.Data.RArray

/-!
# Soundness of finite conjugacy certificates for SL₃(3)

The seven first representatives are the identity, the two nonidentity unipotent
Jordan types, and powers 1, 2, 4, 7 of the fixed Singer matrix. Five auxiliary
representatives have even order, as proved by their power equations. No
pairwise class distinction or externally supplied class table is used.

A certificate supplies a determinant-one matrix k and verifies xk = kr.
Thus x and r are conjugate in the actual special linear group. Boolean tests
reduce in the kernel, and the finite codes use the proved `finiteModelEquiv`.

Source: direct matrix calculation for the class-count input to Guralnick--Malle,
*Classification of 2F-modules I*, Proposition 4.2, manuscript pp.9--10.
-/

namespace Matrix.PSL3Three.OddClassCertificate

@[expose] public def fastMul (a b : Matrix (Fin 3) (Fin 3) (ZMod 3)) :
    Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  fun i j => a i 0 * b 0 j + a i 1 * b 1 j + a i 2 * b 2 j

public theorem fastMul_eq (a b : Matrix (Fin 3) (Fin 3) (ZMod 3)) :
    fastMul a b = a * b := by
  ext i j
  simp [fastMul, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] public def matrixEq (a b : Matrix (Fin 3) (Fin 3) (ZMod 3)) : Bool :=
  (a 0 0).val == (b 0 0).val && (a 0 1).val == (b 0 1).val &&
  (a 0 2).val == (b 0 2).val && (a 1 0).val == (b 1 0).val &&
  (a 1 1).val == (b 1 1).val && (a 1 2).val == (b 1 2).val &&
  (a 2 0).val == (b 2 0).val && (a 2 1).val == (b 2 1).val &&
  (a 2 2).val == (b 2 2).val

public theorem matrixEq_sound {a b : Matrix (Fin 3) (Fin 3) (ZMod 3)}
    (h : matrixEq a b = true) : a = b := by
  simp only [matrixEq, Bool.and_eq_true, beq_iff_eq] at h
  ext i j
  apply Fin.ext
  fin_cases i <;> fin_cases j <;> tauto

@[expose] public def repCode : Fin 12 → MatrixCode :=
  ![6643, 6646, 6889, 2466, 7617, 10083, 6154, 828, 829, 858, 863, 900]

@[expose] public def checkRow (c : MatrixCode) (w : Nat) : Bool :=
  if (codeDet c).val == 1 then
    let k : MatrixCode := ⟨w % 19683, Nat.mod_lt _ (by decide)⟩
    let j : Fin 12 := ⟨w / 19683 % 12, Nat.mod_lt _ (by decide)⟩
    (codeDet k).val == 1 &&
    matrixEq (fastMul (decodeMatrix c) (decodeMatrix k))
      (fastMul (decodeMatrix k) (decodeMatrix (repCode j)))
  else true

@[expose] public def checkRange (f : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => checkRange f start n && f (start + n)

public theorem checkRange_spec (f : Nat → Bool) (start n : Nat) :
    checkRange f start n = true ↔ ∀ k, k < n → f (start + k) = true := by
  induction n with
  | zero => simp [checkRange]
  | succ n ih =>
    rw [checkRange, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, h'⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · exact h k hlt
      · exact h'
    · intro h
      exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h n (Nat.lt_succ_self n)⟩

public theorem rep_det (j : Fin 12) : codeDet (repCode j) = 1 := by
  revert j
  decide +kernel

@[expose] public def representative (j : Fin 12) : SL :=
  finiteModelEquiv ⟨repCode j, rep_det j⟩

public theorem checkRow_sound (c : MatrixCode) (hc : codeDet c = 1) (w : Nat)
    (h : checkRow c w = true) :
    ∃ j : Fin 12, IsConj (finiteModelEquiv ⟨c, hc⟩) (representative j) := by
  let k : MatrixCode := ⟨w % 19683, Nat.mod_lt _ (by decide)⟩
  let j : Fin 12 := ⟨w / 19683 % 12, Nat.mod_lt _ (by decide)⟩
  have he : (codeDet c).val == 1 := by rw [hc]; decide
  simp only [checkRow, he, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h
  have hk : codeDet k = 1 := Fin.ext h.1
  let g : SL := finiteModelEquiv ⟨k, hk⟩
  have hmul : finiteModelEquiv ⟨c, hc⟩ * g = g * representative j := by
    apply Subtype.ext
    exact (fastMul_eq _ _).symm.trans ((matrixEq_sound h.2).trans (fastMul_eq _ _))
  apply Exists.intro j
  apply IsConj.symm
  apply isConj_iff.mpr
  refine ⟨g, ?_⟩
  rw [← hmul, mul_inv_cancel_right]

public theorem checkRange_append {f : Nat → Bool} {start n m : Nat}
    (h₁ : checkRange f start n = true) (h₂ : checkRange f (start + n) m = true) :
    checkRange f start (n + m) = true := by
  apply (checkRange_spec _ _ _).mpr
  intro k hk
  by_cases hkn : k < n
  · exact (checkRange_spec _ _ _).mp h₁ k hkn
  · have h := (checkRange_spec _ _ _).mp h₂ (k - n) (by omega)
    have heq : start + n + (k - n) = start + k := by omega
    simpa only [heq] using h


@[expose] public def evenIndex (i : Fin 5) : Fin 12 := ⟨7 + i.val, by omega⟩
@[expose] public def evenExponent : Fin 5 → Nat := ![4, 6, 8, 8, 2]

private theorem even_powers : ∀ i : Fin 5,
    representative (evenIndex i) ^ evenExponent i = 1 ∧
    representative (evenIndex i) ^ 3 ≠ 1 := by decide +kernel

public theorem even_representative (j : Fin 12) (hj : 7 ≤ j.val) :
    2 ∣ orderOf (representative j) := by
  let i : Fin 5 := ⟨j.val - 7, by omega⟩
  have he : evenIndex i = j := Fin.ext (by dsimp [evenIndex, i]; omega)
  rw [← he]
  obtain ⟨hp, hn⟩ := even_powers i
  have hediv : ∀ k : Fin 5, evenExponent k ∣ 24 := by decide
  have hd : orderOf (representative (evenIndex i)) ∣ 24 :=
    (orderOf_dvd_iff_pow_eq_one.mpr hp).trans (hediv i)
  have harith : ∀ d ≤ 24, d ∣ 24 → ¬ 2 ∣ d → d ∣ 3 := by decide
  by_contra h
  exact hn (orderOf_dvd_iff_pow_eq_one.mp (harith _
    (Nat.le_of_dvd (by decide) hd) hd h))

end Matrix.PSL3Three.OddClassCertificate


