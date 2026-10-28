module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.Words

/-!
# Four odd cyclic subgroups and square fusion in native M₂₄

The representatives have orders 15, 21, 11 and 23. Each representative and
its square-conjugating element is certified by a word in the two standard
generators of the actual Witt-design automorphism group. GAP supplied only
these words; the kernel checks their point actions and all identities.

Powers of these four elements are candidates for covering all odd-order
elements. This file does not assert that coverage. Once coverage is proved,
square fusion will force all characteristic-two traces into the binary field.
The consumer is the degree-eleven field calculation for Guralnick–Malle,
Classification of 2F-modules I, Proposition 5.1, manuscript p.17.

The untrusted generator and retained witnesses are in `source/`. GAP acts on
the right, so its words are reversed on translation to Lean; point 24 is 0.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24OddCyclic

open Words

def representativePerm : Fin 4 → Equiv.Perm (Fin 24)
  | 0 =>
    { toFun := ![20, 21, 19, 14, 8, 12, 22, 18, 6, 13, 9, 4, 0, 10, 16, 3, 1, 5, 2, 15, 7, 17, 11, 23]
      invFun := ![12, 16, 18, 15, 11, 17, 8, 20, 4, 10, 13, 22, 5, 9, 3, 19, 14, 21, 7, 2, 0, 1, 6, 23]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }
  | 1 =>
    { toFun := ![17, 9, 12, 6, 11, 21, 18, 13, 23, 19, 3, 20, 14, 4, 2, 0, 7, 8, 22, 16, 10, 15, 5, 1]
      invFun := ![15, 23, 14, 10, 13, 22, 3, 16, 17, 1, 20, 4, 2, 7, 12, 21, 19, 0, 6, 9, 11, 5, 18, 8]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }
  | 2 =>
    { toFun := ![0, 8, 18, 11, 7, 21, 5, 9, 20, 14, 4, 6, 16, 3, 19, 13, 10, 22, 15, 1, 12, 17, 2, 23]
      invFun := ![0, 19, 22, 13, 10, 6, 11, 4, 1, 7, 16, 3, 20, 15, 9, 18, 12, 21, 2, 14, 8, 5, 17, 23]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }
  | _ =>
    { toFun := ![21, 19, 0, 12, 6, 16, 23, 20, 4, 3, 17, 11, 2, 7, 1, 13, 18, 14, 15, 5, 9, 22, 8, 10]
      invFun := ![2, 14, 12, 9, 8, 19, 4, 13, 22, 20, 23, 11, 3, 15, 17, 18, 5, 10, 16, 1, 7, 0, 21, 6]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }

private def representativeWord : Fin 4 → List (Fin 3)
  | 0 => [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1]
  | 1 => [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0]
  | 2 => [0, 1, 0, 2, 2, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2]
  | _ => [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2]

private theorem representative_word (i : Fin 4) :
    representativePerm i = (evaluate (representativeWord i)).val := by
  have h : ∀ i x, representativePerm i x = wordPoint (representativeWord i) x := by
    decide +kernel
  apply Equiv.ext
  intro x
  rw [evaluate_apply]
  exact h i x

/-- A word-certified element of the native Witt-design group. -/
noncomputable def representative (i : Fin 4) : M24 :=
  ⟨representativePerm i, by exact (representative_word i).symm ▸ (evaluate (representativeWord i)).property⟩

@[simp] theorem representative_val (i : Fin 4) :
    (representative i).val = representativePerm i := rfl

def conjugatorPerm : Fin 4 → Equiv.Perm (Fin 24)
  | 0 =>
    { toFun := ![19, 1, 5, 2, 11, 20, 22, 16, 8, 13, 10, 6, 18, 9, 15, 7, 14, 12, 21, 0, 3, 17, 4, 23]
      invFun := ![19, 1, 3, 20, 22, 2, 11, 15, 8, 13, 10, 4, 17, 9, 16, 14, 7, 21, 12, 0, 5, 18, 6, 23]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }
  | 1 =>
    { toFun := ![22, 1, 2, 23, 18, 11, 9, 20, 0, 19, 17, 5, 14, 3, 12, 6, 4, 21, 16, 7, 15, 10, 13, 8]
      invFun := ![8, 1, 2, 13, 16, 11, 15, 19, 23, 6, 21, 5, 14, 22, 12, 20, 18, 10, 4, 9, 7, 17, 0, 3]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }
  | 2 =>
    { toFun := ![23, 22, 1, 9, 2, 12, 8, 15, 18, 3, 17, 19, 11, 4, 6, 16, 5, 7, 20, 21, 13, 10, 14, 0]
      invFun := ![23, 2, 4, 9, 13, 16, 14, 17, 6, 3, 21, 12, 5, 20, 22, 7, 15, 10, 8, 11, 18, 19, 1, 0]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }
  | _ =>
    { toFun := ![16, 1, 19, 10, 12, 18, 0, 21, 9, 6, 4, 11, 14, 2, 17, 3, 13, 23, 20, 5, 8, 15, 7, 22]
      invFun := ![6, 1, 13, 15, 10, 19, 9, 22, 20, 8, 3, 11, 4, 16, 12, 21, 0, 14, 5, 2, 18, 7, 23, 17]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }

private def conjugatorWord : Fin 4 → List (Fin 3)
  | 0 => [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 2, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1]
  | 1 => [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0]
  | 2 => [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2]
  | _ => [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0]

private theorem conjugator_word (i : Fin 4) :
    conjugatorPerm i = (evaluate (conjugatorWord i)).val := by
  have h : ∀ i x, conjugatorPerm i x = wordPoint (conjugatorWord i) x := by
    decide +kernel
  apply Equiv.ext
  intro x
  rw [evaluate_apply]
  exact h i x

/-- A word-certified element of the native Witt-design group. -/
noncomputable def conjugator (i : Fin 4) : M24 :=
  ⟨conjugatorPerm i, by exact (conjugator_word i).symm ▸ (evaluate (conjugatorWord i)).property⟩

@[simp] theorem conjugator_val (i : Fin 4) :
    (conjugator i).val = conjugatorPerm i := rfl

/-- The same ambient element squares the generator and hence all its powers. -/
theorem conjugator_spec (i : Fin 4) :
    conjugator i * representative i * (conjugator i)⁻¹ = representative i ^ 2 := by
  have h : ∀ i, conjugatorPerm i * representativePerm i * (conjugatorPerm i)⁻¹ =
      representativePerm i ^ 2 := by
    decide +kernel
  exact Subtype.ext (h i)

theorem representative_square_conjugacy (i : Fin 4) :
    IsConj (representative i) (representative i ^ 2) :=
  isConj_iff.mpr ⟨conjugator i, conjugator_spec i⟩

/-- Square fusion on every element of each of the four cyclic subgroups. -/
theorem power_square_conjugacy (i : Fin 4) (n : ℕ) :
    IsConj (representative i ^ n) ((representative i ^ n) ^ 2) := by
  simpa only [← pow_mul, Nat.mul_comm 2 n] using
    IsConj.pow n (representative_square_conjugacy i)

/-- The four chosen generator orders, in the fixed indexing convention. -/
def period : Fin 4 → ℕ := ![15, 21, 11, 23]

theorem representative_order (i : Fin 4) : orderOf (representative i) = period i := by
  have hp : ∀ i, 0 < period i := by decide +kernel
  have hc : ∀ i, representativePerm i ^ period i = 1 ∧
      ∀ n : Fin (period i), 0 < n.val → representativePerm i ^ n.val ≠ 1 := by
    decide +kernel
  rw [← Subgroup.orderOf_coe, orderOf_eq_iff (hp i)]
  exact ⟨(hc i).1, fun n hn hpos => (hc i).2 ⟨n, hn⟩ hpos⟩

end Sporadic.Mathieu.M24OddCyclic
