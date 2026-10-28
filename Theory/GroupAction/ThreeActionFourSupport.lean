module
public import Theory.GroupAction.CommutatorSemidirect
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import Mathlib.GroupTheory.OrderOfElement

/-!
# A moved subgroup generates a four-element order-three action support

Let a group F of order three act by automorphisms on a finite group V,
with full action commutator of order four. If a subgroup A contains a
vector moved by F, its restricted action commutator is the full support.
No elementary-abelian or invariance hypothesis on A is needed.

A moved vector has three distinct points in its orbit. The two differences
from that vector to the other orbit points are distinct and nonidentity,
and both lie in the restricted commutator. Its order therefore is at least
three and divides four, so containment in the full support is equality.

This standard small-action argument supplies the selected omega residual
module containment in Stellmacher (6.4), journal p32, following
refs/latex/stellmacher-n-group.tex. It isolates the order-three counting
argument also used for natural fixed-coordinate modules.
-/

/-- A nonfixed subgroup generates the full four-element support of an order-three action. -/
public theorem three_action_commutator_eq_four_support
    {F V : Type*} [Group F] [Group V] [Finite F] [Finite V]
    [MulDistribMulAction F V] (A : Subgroup V)
    (hF : Nat.card F = 3) (hM : Nat.card (commutatorAction F V) = 4)
    (hA : ¬ A ≤ FixedPoints.subgroup F V) :
    commutatorSubgroup F V A = commutatorAction F V := by
  classical
  obtain ⟨a, haA, hnfix⟩ := SetLike.not_le_iff_exists.mp hA
  obtain ⟨f, hf⟩ : ∃ f : F, f • a ≠ a := not_forall.mp hnfix
  have hf3 : f ^ 3 = 1 := by rw [← hF]; exact pow_card_eq_one' (x := f)
  have hf2 : f ^ 2 • a ≠ a := by
    intro hh
    apply hf
    calc
      f • a = f • (f ^ 2 • a) := by rw [hh]
      _ = f ^ 3 • a := by rw [← mul_smul]; congr 1; group
      _ = a := by rw [hf3, one_smul]
  have hdiff : f ^ 2 • a ≠ f • a := by
    intro hh
    apply hf
    have he := congrArg (fun v : V => f⁻¹ • v) hh
    simpa only [← mul_smul, pow_two, inv_mul_cancel_left, inv_mul_cancel, one_smul] using he
  let C := commutatorSubgroup F V A
  let b := a⁻¹ * (f • a)
  let c := a⁻¹ * (f ^ 2 • a)
  have hb : b ∈ C := Subgroup.subset_closure ⟨f, a, haA, rfl⟩
  have hc : c ∈ C := Subgroup.subset_closure ⟨f ^ 2, a, haA, rfl⟩
  have hbne : b ≠ 1 := by
    intro hh
    exact hf (inv_mul_eq_one.mp hh).symm
  have hcne : c ≠ 1 := by
    intro hh
    exact hf2 (inv_mul_eq_one.mp hh).symm
  have hbc : b ≠ c := by
    intro hh
    exact hdiff (mul_left_cancel hh).symm
  let e : Fin 3 → C := fun i => if i = 0 then 1 else if i = 1 then ⟨b, hb⟩ else ⟨c, hc⟩
  have hinj : Function.Injective e := by
    intro i j hij
    have he := congrArg Subtype.val hij
    clear hij
    fin_cases i <;> fin_cases j <;> simp_all [e]
  have hge : 3 ≤ Nat.card C := by
    simpa using Nat.card_le_card_of_injective e hinj
  have hCM : C ≤ commutatorAction F V := commutatorSubgroup_mono (A := F) le_top
  have hdvd : Nat.card C ∣ 4 := by
    rw [← hM]
    exact Subgroup.card_dvd_of_le hCM
  have hle : Nat.card C ≤ 4 := Nat.le_of_dvd (by decide) hdvd
  have hcard : Nat.card C = 4 := by
    interval_cases h : Nat.card C <;> norm_num at *
  exact Subgroup.eq_of_le_of_card_ge hCM (by rw [hcard, hM])
