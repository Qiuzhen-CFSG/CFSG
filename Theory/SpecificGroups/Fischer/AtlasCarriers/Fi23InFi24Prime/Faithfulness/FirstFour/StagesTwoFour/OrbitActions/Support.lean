module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Setup
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.OrbitActions.DataBase
/-!
# Soundness of intermediate finite action certificates

A table supports a permutation when the labelled points intertwine its action
with table lookup. Kernel checks establish the two basic actions, composition,
and inversion. The multiplication and inverse lemmas compose actual ambient
permutations and require no faithfulness or stabilizer hypothesis.

Source: ATLAS F24G1-p306936B0 and the literal Fischer lift word definitions.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.OrbitActions
abbrev Index := Fin 31671
def ix (t : Nat → Nat) (j : Index) : Index := ⟨t j.val % 31671, Nat.mod_lt _ (by decide)⟩
def lab (j : Index) : Fin 306936 := ⟨Data.labels j.val % 306936, Nat.mod_lt _ (by decide)⟩
def Supports (p : Ambient) (t : Nat → Nat) : Prop := ∀ j, p (lab j) = lab (ix t j)
def baseTest (f t : Nat → Nat) (n : Nat) : Bool :=
  f (Data.labels (n % 31671) % 306936) == Data.labels (t (n % 31671) % 31671) % 306936
def mulTest (t u v : Nat → Nat) (n : Nat) : Bool :=
  t (n % 31671) % 31671 == u (v (n % 31671) % 31671) % 31671
def invTest (t u : Nat → Nat) (n : Nat) : Bool :=
  u (t (n % 31671) % 31671) % 31671 == n % 31671

theorem base_support (p : Ambient) (f t : Nat → Nat)
    (hf : ∀ x, (p x).val = f x.val)
    (hc : ∀ j : Index, baseTest f t j.val = true) : Supports p t := by
  intro j
  apply Fin.ext
  rw [hf]
  have h := hc j
  simpa only [baseTest, Nat.mod_eq_of_lt j.isLt, beq_iff_eq, lab, ix] using h

theorem mul_support (p q : Ambient) (t u v : Nat → Nat)
    (hp : Supports p u) (hq : Supports q v)
    (hc : ∀ j : Index, mulTest t u v j.val = true) : Supports (p * q) t := by
  intro j
  rw [Equiv.Perm.mul_apply, hq, hp]
  congr 1
  apply Fin.ext
  have h := hc j
  simp only [mulTest, Nat.mod_eq_of_lt j.isLt, beq_iff_eq] at h
  exact h.symm

theorem inv_support (p : Ambient) (t u : Nat → Nat)
    (hp : Supports p u) (hc : ∀ j : Index, invTest t u j.val = true) : Supports p⁻¹ t := by
  intro j
  apply p.injective
  change p (p.symm (lab j)) = p (lab (ix t j))
  rw [Equiv.apply_symm_apply, hp]
  congr 1
  apply Fin.ext
  have h := hc j
  simp only [invTest, Nat.mod_eq_of_lt j.isLt, beq_iff_eq] at h
  exact h.symm

theorem checked (f : Nat → Bool) (hc : Certificate.checkPow f 0 15 = true)
    (j : Index) : f j.val = true :=
  Certificate.checkPow_sound f 15 0 hc j.val (Nat.zero_le _) (by have := j.isLt; omega)
end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.OrbitActions
