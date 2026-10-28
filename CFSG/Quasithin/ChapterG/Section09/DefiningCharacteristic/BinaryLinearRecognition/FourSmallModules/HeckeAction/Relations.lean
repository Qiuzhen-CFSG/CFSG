module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.HeckeAction.Basic

/-!
# Preservation and braid for binary SL₄ root operators

Positive-root conjugation shows that each simple operator preserves the
upper-fixed subspace. Expanding the two adjacent triple products gives the
same eight group elements, proving the braid relation on the whole module.
The finite matrix identities are checked by kernel reduction.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
G.9.3(11)--(12), printed pp.354,356--357. The elementary root proofs adapt
the binary SL₅ highest-vector development in this repository to rank three.
-/

@[expose] public section

open Representation
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.HeckeAction

private def positive (a b : Fin 4) : Group :=
  if h : a < b then Matrix.SpecialLinearGroup.transvection (ne_of_lt h) (1 : ZMod 2)
  else 1

private theorem conjugate_swap (i : Fin 3) (a b : Fin 4) (h : a < b)
    (hne : ¬ (a = i.castSucc ∧ b = i.succ)) :
    positive a b * simpleSwap i = simpleSwap i *
      positive (Equiv.swap i.castSucc i.succ a) (Equiv.swap i.castSucc i.succ b) := by
  revert i a b
  decide

private theorem conjugate_lower (i : Fin 3) (a b : Fin 4) (h : a < b)
    (hne : ¬ (a = i.castSucc ∧ b = i.succ)) :
    positive a b * simpleLower i = simpleLower i *
      (positive a b *
       ((if a = i.castSucc then positive i.succ b else 1) *
        (if b = i.succ then positive a i.castSucc else 1))) := by
  revert i a b
  decide

private theorem upper_lower (i : Fin 3) :
    simpleUpper i * simpleLower i = simpleSwap i * simpleUpper i := by
  revert i
  decide


private def term (i : Fin 3) (b : Bool) : Group :=
  if b then simpleUpper i * simpleSwap i else simpleSwap i

private theorem word_braid (i j : Fin 3) (hij : i.val + 1 = j.val)
    (a b c : Bool) :
    term i a * (term j b * term i c) =
      term j c * (term i (b ^^ (a && c)) * term j a) := by
  revert i j a b c
  decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
private theorem act_mul (ρ : Representation (ZMod 2) Group V) (g h : Group) (v : V) :
    ρ g (ρ h v) = ρ (g * h) v := by rw [map_mul]; rfl

private theorem operator_terms (ρ : Representation (ZMod 2) Group V) (i : Fin 3) (v : V) :
    operator ρ i v = ρ (term i false) v + ρ (term i true) v := by
  rw [operator_apply, act_mul]
  rfl

/-- Adjacent root operators satisfy braid on the entire ambient representation. -/
theorem operator_braid (ρ : Representation (ZMod 2) Group V)
    (i j : Fin 3) (hij : i.val + 1 = j.val) (v : V) :
    operator ρ i (operator ρ j (operator ρ i v)) =
      operator ρ j (operator ρ i (operator ρ j v)) := by
  simp only [operator_terms, map_add, act_mul, word_braid i j hij]
  simp only [Bool.false_and, Bool.true_and, Bool.xor_false, Bool.xor_true,
    Bool.not_false, Bool.not_true]
  abel

private theorem positive_fixed (ρ : Representation (ZMod 2) Group V)
    {v : V} (hv : UpperFixed ρ v) (a b : Fin 4) : ρ (positive a b) v = v := by
  unfold positive
  split_ifs with h
  · exact hv a b h
  · simp

/-- Each simple root operator preserves the vectors fixed by all positive roots. -/
theorem operator_upperFixed (ρ : Representation (ZMod 2) Group V)
    (i : Fin 3) {v : V} (hv : UpperFixed ρ v) : UpperFixed ρ (operator ρ i v) := by
  intro a b hab
  have hp : positive a b =
      Matrix.SpecialLinearGroup.transvection (ne_of_lt hab) (1 : ZMod 2) := dif_pos hab
  rw [← hp]
  rw [operator_apply_of_upperFixed ρ i hv, map_add, act_mul, act_mul]
  by_cases he : a = i.castSucc ∧ b = i.succ
  · obtain ⟨rfl, rfl⟩ := he
    have hu : ρ (simpleUpper i) v = v := hv i.castSucc i.succ (by simp)
    have hs : positive i.castSucc i.succ = simpleUpper i := by
      simp only [positive, dif_pos (show i.castSucc < i.succ by simp)]
      rfl
    rw [hs]
    rw [upper_mul_swap, upper_lower]
    simp only [map_mul, Module.End.mul_apply, hu]
    exact add_comm _ _
  · rw [conjugate_swap i a b hab he, conjugate_lower i a b hab he]
    split_ifs <;>
      simp only [map_mul, Module.End.mul_apply, map_one, Module.End.one_apply,
        positive_fixed ρ hv]

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.HeckeAction
