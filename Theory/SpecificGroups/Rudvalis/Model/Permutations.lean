module

public import Theory.SpecificGroups.Rudvalis.Model.PermutationData

/-!
# Checked Rudvalis permutation generators

We check the inverse laws and standard-generator word relations against the
ATLAS degree-4060 tables. All finite computations use kernel reduction.
Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Ru/ . The relations
listed there are a semi-presentation, not a presentation or a recognition
theorem. Only their validity for these explicit permutations is asserted here.
-/

namespace Rudvalis

set_option maxRecDepth 30000

namespace Data

/-- Boolean enumeration used by pointwise permutation certificates. -/
@[expose] public def checkNat (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => checkNat f n && f n

private theorem checkNat_spec (f : Nat → Bool) (n : Nat) :
    checkNat f n = true ↔ ∀ i, i < n → f i = true := by
  induction n with
  | zero => simp [checkNat]
  | succ n ih =>
    rw [checkNat, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, h'⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact h i hlt
      · exact h'
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

/-- Soundness of finite Boolean checking on the 4060 letters. -/
public theorem allFin (P : Fin 4060 → Prop) [DecidablePred P]
    (h : checkNat (fun k => decide (P ⟨k % 4060, Nat.mod_lt _ (by decide)⟩)) 4060 = true) :
    ∀ i, P i := by
  rintro ⟨k, hk⟩
  have h' := of_decide_eq_true ((checkNat_spec _ _).mp h k hk)
  simpa only [Nat.mod_eq_of_lt hk] using h'

public theorem aMap_involutive : ∀ x, aMap (aMap x) = x := by
  apply allFin
  decide +kernel

public theorem bMap_fourth : ∀ x, bMap (bMap (bMap (bMap x))) = x := by
  apply allFin
  decide +kernel

public theorem abMap_eq : ∀ x, abMap x = aMap (bMap x) := by
  apply allFin
  decide +kernel

public theorem wMap_eq : ∀ x, wMap x = aMap (bMap (aMap (bMap (bMap x)))) := by
  apply allFin
  decide +kernel

end Data

/-- ATLAS generator `a`, converted to the left-action convention. -/
@[expose] public def aPerm : Equiv.Perm (Fin 4060) where
  toFun := Data.aMap
  invFun := Data.aMap
  left_inv := Data.aMap_involutive
  right_inv := Data.aMap_involutive

/-- ATLAS generator `b`, converted to the left-action convention. -/
@[expose] public def bPerm : Equiv.Perm (Fin 4060) where
  toFun := Data.bMap
  invFun x := Data.bMap (Data.bMap (Data.bMap x))
  left_inv := Data.bMap_fourth
  right_inv := Data.bMap_fourth

public theorem aPerm_sq : aPerm ^ 2 = 1 := by
  apply Equiv.ext
  intro x
  exact Data.aMap_involutive x

public theorem bPerm_fourth : bPerm ^ 4 = 1 := by
  apply Equiv.ext
  intro x
  exact Data.bMap_fourth x

public theorem abPerm_thirteenth : (aPerm * bPerm) ^ 13 = 1 := by
  apply Equiv.ext
  change ∀ x, ((aPerm * bPerm) ^ 13) x = x
  rw [Equiv.Perm.coe_pow]
  have h : ⇑(aPerm * bPerm) = Data.abMap := funext (fun x => (Data.abMap_eq x).symm)
  rw [h]
  apply Data.allFin
  decide +kernel

public theorem ababbPerm_twentyNinth :
    (aPerm * bPerm * aPerm * bPerm * bPerm) ^ 29 = 1 := by
  apply Equiv.ext
  change ∀ x, ((aPerm * bPerm * aPerm * bPerm * bPerm) ^ 29) x = x
  rw [Equiv.Perm.coe_pow]
  have h : ⇑(aPerm * bPerm * aPerm * bPerm * bPerm) = Data.wMap :=
    funext (fun x => (Data.wMap_eq x).symm)
  rw [h]
  apply Data.allFin
  decide +kernel

end Rudvalis
