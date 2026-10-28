module

public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.WordCertificates.Tables
/-!
# Soundness of finite action and power checks

Boolean equality checks enumerate all 4928 points, and the resulting function
identities certify permutation powers. These elementary reflection lemmas
connect the finite word checks to the literal ATLAS permutations; the Python
lookup generator supplies no trusted mathematical assertions.
-/

@[expose] public section

namespace Sporadic.Mathieu.M22CyclicFour.WordCertificates

def checkEq (f g : Fin 4928 → Fin 4928) : Bool :=
  (List.range 4928).all fun i => decide (f (point i) = g (point i))

theorem point_val (i : Fin 4928) : point i.val = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem eq_of_check (f g : Fin 4928 → Fin 4928) (h : checkEq f g = true)
    (i : Fin 4928) : f i = g i := by
  have hi := of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  simpa only [point_val] using hi

def iter (f : Fin 4928 → Fin 4928) : Nat → Fin 4928 → Fin 4928
  | 0, x => x
  | n + 1, x => f (iter f n x)

theorem pow_action (p : Equiv.Perm (Fin 4928)) (f : Fin 4928 → Fin 4928)
    (h : ∀ x, p x = f x) (n : Nat) (x : Fin 4928) : (p ^ n) x = iter f n x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, h]; rfl

theorem pow_eq_one_of_check (p : Equiv.Perm (Fin 4928)) (f : Fin 4928 → Fin 4928)
    (h : ∀ x, p x = f x) (n : Nat) (hc : checkEq (iter f n) id = true) : p ^ n = 1 := by
  apply Equiv.ext
  intro x
  exact (pow_action p f h n x).trans (eq_of_check _ _ hc x)

end Sporadic.Mathieu.M22CyclicFour.WordCertificates
