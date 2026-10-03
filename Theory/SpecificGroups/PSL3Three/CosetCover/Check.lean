module

public import Theory.SpecificGroups.PSL3Three.RepresentativeBounds
public import Theory.SpecificGroups.PSL3Three.AmbientGenerators
public import Init.Data.RArray

/-!
# Boolean checks for the SL₃(3) coset certificates

Entrywise Boolean equality avoids constructing equality proofs at every matrix
entry during reduction. The soundness lemmas turn the reduced checks into actual
matrix equations and universal statements. The checks are evaluated by Lean's
kernel; the external coset enumeration supplies only candidate data.

Source: the right-coset transition criterion in `SubgroupEnumeration`.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.CosetCheck

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

public theorem checkRange_fin {n : Nat} (hn : 0 < n) (f : Fin n → Bool)
    (h : checkRange (fun k => f ⟨k % n, Nat.mod_lt _ hn⟩) 0 n = true) :
    ∀ i, f i = true := by
  intro ⟨i, hi⟩
  have h' := (checkRange_spec _ _ _).mp h i hi
  simpa only [Nat.zero_add, Nat.mod_eq_of_lt hi] using h'

end Matrix.PSL3Three.CertifiedEnumeration.CosetCheck
