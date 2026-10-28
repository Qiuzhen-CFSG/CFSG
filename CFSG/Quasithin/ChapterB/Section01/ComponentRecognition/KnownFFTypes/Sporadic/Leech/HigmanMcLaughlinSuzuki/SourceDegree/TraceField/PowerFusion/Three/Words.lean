module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Base
public import Mathlib.NumberTheory.Divisors

/-!
# Cubic and fifteen-element witnesses for HS square fusion

The cubic and its commuting conjugate are the words used by `HS.ThreeRank`.
The ATLAS word `ababb` has order fifteen. Explicit carrier words conjugate its
fifth power to the chosen cubic and conjugate it to its square. Eight further
words fuse the nonidentity elements of the resulting nine-group.

GAP supplies only words; every identity is checked on all 100 letters by Lean's
kernel, using the inverse-generator left-action convention. The discovery
script is retained in `source/`. Source: ATLAS HSG1-p100B0 and
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/HS/.
-/

public section
namespace Sporadic.LeechRelated.HS.ThreePowerFusion
open OrderCertificate Theory.GroupTheory

@[expose] def a : Carrier := ⟨p0, by rw [a_eq_generator]; exact Subgroup.subset_closure (by simp)⟩
@[expose] def b : Carrier := ⟨p1, by rw [b_eq_generator]; exact Subgroup.subset_closure (by simp)⟩
@[expose] def cubic : Carrier := (a * b ^ 2 * a * b ^ 3) ^ 2
private def translate : Carrier :=
  (a * b) * (a * b ^ 2) * (a * b) * (a * b) * (a * b ^ 2) * (a * b ^ 4)
def cubicMate : Carrier := translate * cubic * translate⁻¹
private def letter (i : Fin 3) : Carrier := if i = 0 then a else if i = 1 then b else b⁻¹

private def fusionWord (i j : Fin 3) : List (Fin 3) :=
  match i.val, j.val with
  | 0, 1 => [1, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 2, 0, 1, 0, 2, 2, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 2, 0, 1, 1, 1]
  | 0, 2 => [1, 0, 1, 1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 1, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 2]
  | 1, 0 => []
  | 1, 1 => [2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0]
  | 1, 2 => [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1]
  | 2, 0 => [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 2]
  | 2, 1 => [1, 0, 1, 1, 0, 2, 0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1]
  | 2, 2 => [0, 1, 1, 0, 2, 2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1]
  | _, _ => []

theorem cubic_cube : cubic ^ 3 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

theorem cubic_ne_one : cubic ≠ 1 := by
  intro h
  have he := congrArg (fun z : Carrier => inclusion z 0) h
  exact (by decide +kernel : inclusion cubic 0 ≠ 0) he

theorem cubic_order : orderOf cubic = 3 := orderOf_eq_prime cubic_cube cubic_ne_one

theorem cubicMate_cube : cubicMate ^ 3 = 1 := by
  simpa only [MulAut.conj_apply, cubicMate] using
    (map_pow (MulAut.conj translate) cubic 3).symm.trans
      ((congrArg (MulAut.conj translate) cubic_cube).trans (map_one _))

theorem cubic_commute : Commute cubic cubicMate := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

theorem witness_images :
    inclusion cubic 0 = 94 ∧ inclusion (cubic ^ 2) 0 = 59 ∧ inclusion cubicMate 0 = 15 := by
  decide +kernel

private theorem fusion_word_eq : ∀ i j : Fin 3, i ≠ 0 ∨ j ≠ 0 →
    evalWord letter (fusionWord i j) * cubic * (evalWord letter (fusionWord i j))⁻¹ =
      cubic ^ i.val * cubicMate ^ j.val := by
  have h : ∀ i j : Fin 3, ∀ t : Fin 100, i ≠ 0 ∨ j ≠ 0 →
      inclusion (evalWord letter (fusionWord i j) * cubic *
        (evalWord letter (fusionWord i j))⁻¹) t =
      inclusion (cubic ^ i.val * cubicMate ^ j.val) t := by
    apply allFin
    decide +kernel
  intro i j hij
  apply Subtype.ext
  apply Equiv.ext
  intro t
  exact h i j t hij

/-- All eight nonidentity words in the nine-group are conjugate to the cubic. -/
theorem cubic_fusion (i j : Fin 3) (h : i ≠ 0 ∨ j ≠ 0) :
    IsConj cubic (cubic ^ i.val * cubicMate ^ j.val) :=
  isConj_iff.mpr ⟨evalWord letter (fusionWord i j), fusion_word_eq i j h⟩

/-- Square fusion for the distinguished cubic, with a literal carrier witness. -/
theorem cubic_square : IsConj cubic (cubic ^ 2) := by
  simpa using cubic_fusion 2 0 (Or.inl (by decide))

private def fifteenWord : Carrier := a * b * a * b * b
private def transport : Carrier := evalWord letter [1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1]
private def squareActor : Carrier := evalWord letter [1, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 1]

/-- A conjugate of the ATLAS fifteen-element whose fifth power is `cubic`. -/
def fifteen : Carrier := transport * fifteenWord * transport⁻¹

private theorem fifteenWord_pow : fifteenWord ^ 15 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem fifteenWord_order : orderOf fifteenWord = 15 := by
  have hdiv := orderOf_dvd_of_pow_eq_one fifteenWord_pow
  have h3 : fifteenWord ^ 3 ≠ 1 := by
    intro h
    have he := congrArg (fun z : Carrier => inclusion z 0) h
    exact (by decide +kernel : inclusion (fifteenWord ^ 3) 0 ≠ 0) he
  have h5 : fifteenWord ^ 5 ≠ 1 := by
    intro h
    have he := congrArg (fun z : Carrier => inclusion z 0) h
    exact (by decide +kernel : inclusion (fifteenWord ^ 5) 0 ≠ 0) he
  have hm := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 15 ≠ 0)⟩
  have hd : Nat.divisors 15 = {1, 3, 5, 15} := by decide
  rw [hd] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h
  · exact (h3 (orderOf_dvd_iff_pow_eq_one.mp (h ▸ (by decide : 1 ∣ 3)))).elim
  · exact (h3 (h ▸ pow_orderOf_eq_one fifteenWord)).elim
  · exact (h5 (h ▸ pow_orderOf_eq_one fifteenWord)).elim
  · exact h

theorem fifteen_order : orderOf fifteen = 15 := by
  change orderOf (MulAut.conj transport fifteenWord) = 15
  rw [MulEquiv.orderOf_eq]
  exact fifteenWord_order

theorem fifteen_fifth : fifteen ^ 5 = cubic := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- Square fusion for the chosen fifteen-element. -/
theorem fifteen_square : IsConj fifteen (fifteen ^ 2) := by
  have h : IsConj fifteenWord (fifteenWord ^ 2) := by
    apply isConj_iff.mpr
    refine ⟨squareActor, ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    apply allFin
    decide +kernel
  have hc : IsConj fifteenWord fifteen := isConj_iff.mpr ⟨transport, rfl⟩
  exact (hc.symm.trans h).trans (hc.pow 2)

end Sporadic.LeechRelated.HS.ThreePowerFusion
