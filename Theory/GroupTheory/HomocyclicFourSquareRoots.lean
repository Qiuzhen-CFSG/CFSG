module
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Recognizing homocyclic abelian groups of exponent four

In a finite abelian group of exponent four, if every involution is a square,
then each nontrivial cyclic factor has order four. The group order fixes
the number of factors. This is the abelian recognition step in the
homocyclic core of Aschbacher--Smith 14.3.33(1), printed p.1004.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory

/-- Exponent four and square roots of all involutions force C₄ⁿ. -/
theorem homocyclic_four_of_square_roots {A : Type*} [Group A] [Finite A]
    [IsMulCommutative A] (n : ℕ) (hcard : Nat.card A = 4 ^ n)
    (hfour : ∀ a : A, a ^ 4 = 1)
    (hroot : ∀ a : A, a ^ 2 = 1 → ∃ b : A, b ^ 2 = a) :
    Nonempty (A ≃* (Fin n → Multiplicative (ZMod 4))) := by
  classical
  let : CommGroup A := IsMulCommutative.instCommGroup
  obtain ⟨ι, hι, d, hd, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  let B (i : ι) := Multiplicative (ZMod (d i))
  have hBfour (i : ι) (b : B i) : b ^ 4 = 1 := by
    obtain ⟨a, ha⟩ := e.surjective (Function.update 1 i b)
    have hh := congrArg (fun a : A => e a i) (hfour a)
    simpa only [map_pow, map_one, Pi.pow_apply, Pi.one_apply, ha, Function.update_self] using hh
  have hBroot (i : ι) (b : B i) (hb : b ^ 2 = 1) : ∃ c : B i, c ^ 2 = b := by
    let x : ∀ i, B i := Function.update 1 i b
    have hx : x ^ 2 = 1 := by
      ext j
      by_cases hj : j = i
      · subst j; simpa [x] using hb
      · simp [x, hj]
    have ha : (e.symm x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
    obtain ⟨a, ha⟩ := hroot (e.symm x) ha
    refine ⟨e a i, ?_⟩
    have hh := congrArg (fun a : A => e a i) ha
    simpa only [map_pow, Pi.pow_apply, e.apply_symm_apply, x, Function.update_self] using hh
  have hd4 (i : ι) : d i = 4 := by
    let : NeZero (d i) := ⟨by have := hd i; omega⟩
    have hdiv : d i ∣ 4 := by
      have hh := (Monoid.exponent_dvd_iff_forall_pow_eq_one (G := B i)).mpr (hBfour i)
      rw [IsCyclic.exponent_eq_card] at hh
      simpa [B] using hh
    have hcases : d i = 2 ∨ d i = 4 := by
      obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp (show d i ∣ 2 ^ 2 from hdiv)
      have hlo := hd i
      interval_cases k <;> norm_num at he <;> omega
    rcases hcases with htwo | hfour
    · have hcardB : Nat.card (B i) = 2 := by simp [B, htwo]
      have hall (b : B i) : b = 1 := by
        have hb : b ^ 2 = 1 := by simpa only [hcardB] using pow_card_eq_one' (x := b)
        obtain ⟨c, rfl⟩ := hBroot i b hb
        simpa only [hcardB] using pow_card_eq_one' (x := c)
      let : Subsingleton (B i) := ⟨fun a b => (hall a).trans (hall b).symm⟩
      have hc : Nat.card (B i) = 1 := Nat.card_unique
      omega
    · exact hfour
  let f : A ≃* (ι → Multiplicative (ZMod 4)) := e.trans
    (MulEquiv.piCongrRight (fun i => by rw [hd4 i]))
  have hn : Fintype.card ι = n := by
    have hc := (Nat.card_congr f.toEquiv).symm.trans hcard
    have hc' : 4 ^ Fintype.card ι = 4 ^ n := by
      simpa [Nat.card_eq_fintype_card] using hc
    exact Nat.pow_right_injective (by decide : 1 < 4) hc'
  let r := (Fintype.equivFinOfCardEq hn).symm
  let reindex : (ι → Multiplicative (ZMod 4)) ≃* (Fin n → Multiplicative (ZMod 4)) := {
    __ := (Equiv.piCongrLeft (fun _ : ι => Multiplicative (ZMod 4)) r).symm
    map_mul' := fun _ _ => rfl }
  exact ⟨f.trans reindex⟩

end Theory.GroupTheory
