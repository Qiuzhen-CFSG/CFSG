module
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoComplement.Binary
import Mathlib.Tactic.FinCases

/-!
# Lower rows of arbitrary central-line lifts

An additive map of the twelve binary coordinates fixing the last basis vector
has a lower coordinate equal to that input coordinate plus a linear functional
of the first eleven. Binary basis expansion identifies this functional with
its eleven values on basis vectors. Applied to both generators, this gives the
22 entries used by the explicit word certificate, in its X-then-Y order.

The basis identity is reduced by the kernel; all other statements are elementary
additive algebra. This is the coordinate step in the module-cover argument of
Aschbacher–Smith I.1.5, printed p.408, for the ATLAS J4 max1 core.
-/

@[expose] public section
namespace Janko4.TwoPrimary.InvariantComplement

def basisVector (i : Fin 11) : V := BitVec.ofNat 11 (2 ^ i.val)

set_option maxRecDepth 10000 in
private theorem basisVector_expansion : ∀ v : V, substitute basisVector v = v := by
  decide +kernel

private theorem map_fold {n : ℕ} (f : BitVec n → Bool) (h0 : f 0 = 0)
    (hadd : ∀ u v, f (u ^^^ v) = f u + f v) (l : List (BitVec n)) :
    f (l.foldr (· ^^^ ·) 0) = (l.map f).sum := by
  induction l with
  | nil => exact h0
  | cons a l ih => simp only [List.foldr_cons, hadd, ih, List.map_cons, List.sum_cons]

theorem xor_hom_expansion (f : V → Bool) (h0 : f 0 = 0)
    (hadd : ∀ u v, f (u ^^^ v) = f u + f v) (v : V) :
    f v = evalRow (fun i => f (basisVector i)) v := by
  conv_lhs => rw [← basisVector_expansion v]
  rw [substitute, map_fold f h0 hadd, List.map_ofFn, List.sum_ofFn]
  change (∑ i, f (if v.getLsbD i.val then basisVector i else 0)) = _
  apply Finset.sum_congr rfl
  intro i _
  cases v.getLsbD i.val
  · change f 0 = 0 * f (basisVector i)
    rw [h0, zero_mul]
  · change f (basisVector i) = 1 * f (basisVector i)
    rw [one_mul]

/-- Indexing the lower rows in the same X-then-Y order as the certificate. -/
def lowerRows (a b : Fin 11 → Bool) : Fin 22 → Bool := Fin.append a b

private theorem evalRow_inputMask (d : Fin 22 → Bool) (s : Bool) (i : Fin 11) :
    evalRow d (inputMask s i) = d ⟨i.val + if s then 11 else 0, by
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩ := by
  cases s <;> fin_cases i <;>
    simp [evalRow, inputMask, Fin.sum_univ_succ, Bool.mul_eq_and, Bool.add_eq_xor]

theorem lowerRows_input (a b : Fin 11 → Bool) (s : Bool) (v : V) :
    evalRow (lowerRows a b) (inputVector s v) = evalRow (if s then b else a) v := by
  rw [inputVector, evalRow_substitute]
  congr 1
  funext i
  rw [evalRow_inputMask]
  cases s
  · change Fin.append a b (Fin.castAdd 11 i) = a i
    exact Fin.append_left _ _ _
  · simpa only [lowerRows, Fin.natAdd, Nat.add_comm, ↓reduceIte] using
      Fin.append_right a b i

/-- Any additive map of the twelve-space fixing its central vector has the
prescribed lower-row form. The quotient action is kept as an explicit premise. -/
theorem exists_lowerRows (F : Bool → (V × Bool) → V × Bool)
    (h0 : ∀ s, F s (0, false) = (0, false))
    (hadd : ∀ s u v, F s (u.1 ^^^ v.1, u.2 + v.2) =
      ((F s u).1 ^^^ (F s v).1, (F s u).2 + (F s v).2))
    (hz : ∀ s, F s (0, true) = (0, true))
    (hquot : ∀ s v, (F s v).1 = quotientStep s v.1) :
    ∃ d : Fin 22 → Bool, ∀ s v, F s v = liftStep d s v := by
  let f (s : Bool) (v : V) : Bool := (F s (v, false)).2
  have hf0 (s : Bool) : f s 0 = 0 := congrArg Prod.snd (h0 s)
  have hfadd (s : Bool) (u v : V) : f s (u ^^^ v) = f s u + f s v :=
    congrArg Prod.snd (hadd s (u, false) (v, false))
  let d := lowerRows (fun i => f false (basisVector i)) (fun i => f true (basisVector i))
  refine ⟨d, ?_⟩
  intro s v
  apply Prod.ext (hquot s v)
  change (F s v).2 = v.2 + evalRow d (inputVector s v.1)
  have hd : evalRow d (inputVector s v.1) = f s v.1 := by
    rw [lowerRows_input]
    cases s <;> exact (xor_hom_expansion _ (hf0 _) (hfadd _) _).symm
  rw [hd]
  have hv := congrArg Prod.snd (hadd s (v.1, false) (0, v.2))
  simp only [← Bool.zero_eq_false, zero_add] at hv
  change (F s (v.1 ^^^ 0#11, v.2)).2 = f s v.1 + (F s (0, v.2)).2 at hv
  rw [BitVec.xor_zero] at hv
  rw [hv]
  have ht : (F s (0, v.2)).2 = v.2 := by
    cases v.2
    · exact congrArg Prod.snd (h0 s)
    · exact congrArg Prod.snd (hz s)
  rw [ht]
  exact add_comm _ _

end Janko4.TwoPrimary.InvariantComplement
