module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.InvolutionCentralizer.Checks
public import Theory.GroupTheory.ConjugacyClassSize
public import Mathlib.Order.Fin.Basic

/-!
# A certified lower bound for the involution conjugacy class

The checked adjacent inequalities make the two-letter keys strictly increasing.
The corresponding 8722 model conjugates therefore inject into the conjugacy
class of a. Orbit–stabilizer gives the same lower bound on the index of its
ordinary ambient centralizer. This proof assumes no numerical group orders.

Source: ATLAS J3G1-p6156B0; GLS3 Table 5.3h, printed p.269.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.InvolutionCertificate
open Sporadic.Janko3 Sporadic.Janko3.OrderCertificate

private theorem rowCorrect (i : Fin 8722) :
    RowCorrect i.val := by
  let b : Fin 69 := ⟨i.val / 128, by have := i.isLt; omega⟩
  let j : Fin 128 := ⟨i.val % 128, Nat.mod_lt _ (by decide)⟩
  have hb := allFin (fun j : Fin 128 =>
    128 * b.val + j.val < 8722 → RowCorrect (128 * b.val + j.val)) (checked_blocks b) j
  have heq : 128 * b.val + j.val = i.val := by
    dsimp [b, j]
    omega
  rw [heq] at hb
  exact hb i.isLt

public theorem index_lower_bound :
    8722 ≤ (Subgroup.centralizer ({a} : Set Model)).index := by
  have hmono : StrictMono (fun i : Fin 8722 => imageKey i.val) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    exact (rowCorrect i.castSucc).2 (Nat.succ_lt_succ i.isLt)
  let v : Fin 8722 → (ConjClasses.mk a).carrier :=
    fun i => ⟨wordConjugate 30 (wordCode i.val), wordConjugate_isConj _ _⟩
  have hv : Function.Injective v := by
    intro i j hij
    apply hmono.injective
    change imageKey i.val = imageKey j.val
    rw [← (rowCorrect i).1, ← (rowCorrect j).1]
    simpa only [wordKey_spec] using congrArg
      (fun x : (ConjClasses.mk a).carrier => modelKey (x : Model)) hij
  have hc := Nat.card_le_card_of_injective v hv
  simpa only [Nat.card_fin, ConjClasses.nat_card_carrier_eq_index_centralizer] using hc
end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.InvolutionCertificate
